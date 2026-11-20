import json
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

from eval.pipeline.completion import run
from eval.pipeline.jsonl import repair_tail
from eval.pipeline.manifests import translation_manifest
from eval.pipeline.task_profile import TaskProfile
from eval.pipeline.translation.batch_run import main as batch_main
from eval.pipeline.translation.verify_generated import _verify_file
from eval.pipeline.verify import verify_translation_record
from itpeval.backends.registry import curated_project, curated_task
from itpeval.core.episodes import Episode
from itpeval.core.types import VerificationEvidence
from itpeval.environments import prepare_project
from itpeval.learning.episodes import export_jsonl, replay
from itpeval.learning.example import run as run_episode
from itpeval.learning.manifests import RunManifest
from itpeval.learning.huggingface import VerifierReward
from itpeval.learning.rewards import proof_reward
from itpeval.learning.views import repair_rows, sample_tasks, trajectory_rows
from itpeval.verification.service import verify


class EvaluationContractTests(unittest.TestCase):
    def test_sample_identity_ignores_duplicates_and_iteration_order(self):
        tasks = [curated_task("metamath", "first"), curated_task("metamath", "second")]
        self.assertEqual(sample_tasks(tasks, count=2, seed=7), sample_tasks(reversed(tasks * 2), count=2, seed=7))
        with self.assertRaisesRegex(ValueError, "distinct tasks"):
            sample_tasks(tasks * 2, count=3, seed=7)

    def test_new_resume_rejects_policy_seed_and_budget_changes(self):
        manifest = RunManifest(("task",), ("env",), "policy", "dataset", "prompt", {"model": "local"}, 0,
                               {"max_attempts": 1})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "out.jsonl"
            manifest.bind(path)
            manifest.bind(path)
            for alternate in (replace(manifest, seed=42), replace(manifest, policy="different"),
                              replace(manifest, budgets={"max_attempts": 2})):
                with self.assertRaisesRegex(ValueError, "manifest mismatch"):
                    alternate.bind(path)
            legacy = Path(directory) / "old.jsonl"
            legacy.write_text('{"verified":true}\n')
            with self.assertRaisesRegex(ValueError, "no run manifest"):
                manifest.bind(legacy)

    def test_legacy_full_file_checkpoint_binds_the_generated_prompt_and_model(self):
        model = {"id": "one", "label": "same", "provider": "local"}
        pair = {"source": "source", "theorem_id": 1, "title": "T", "src_prover": "lean4",
                "tgt_prover": "rocq", "source_sha256": "old", "src_content": "one"}
        def manifest(pair, model):
            return translation_manifest([model], [pair], "proofs", 1, 0.0, 100, True)
        first = manifest(pair, model)
        self.assertNotEqual(first.run_id, manifest({**pair, "src_content": "two"}, model).run_id)
        self.assertNotEqual(first.run_id, manifest(pair, {**model, "id": "two"}).run_id)

    def test_interrupted_checkpoint_keeps_every_complete_row(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.jsonl"
            row = b'{"sample_idx":1}\n'
            path.write_bytes(row + b'{"sam')
            repair_tail(path)
            self.assertEqual(path.read_bytes(), row)
            path.write_bytes(row + b'{"sample_idx":2}')
            repair_tail(path)
            self.assertEqual(len(path.read_bytes().splitlines()), 2)

    def test_reward_requires_complete_bound_proof(self):
        task = curated_task("metamath", "env")
        evidence = VerificationEvidence(task.task_id, task.environment_id, "", "timeout", "not_run", None,
                                        "unchecked", "unknown")
        self.assertIsNone(proof_reward(task, evidence).value)
        with self.assertRaisesRegex(ValueError, "missing"):
            proof_reward(task, replace(evidence, task_success=True))
        with self.assertRaisesRegex(ValueError, "another task"):
            proof_reward(task, replace(evidence, task_id="forged"))
        self.assertEqual(proof_reward(task, replace(evidence, execution_outcome="exited",
                                                    checker_outcome="rejected", task_success=False)).value, 0)
        with self.assertRaisesRegex(ValueError, "trusted task"):
            verify_translation_record({"task_id": task.task_id, "generated": "..."})

    @unittest.skipUnless(os.environ.get("ITPEVAL_CONFORMANCE_PROVER"), "select an installed real prover")
    def test_sdk_sync_batch_posthoc_and_trainer_agree(self):
        prover = os.environ["ITPEVAL_CONFORMANCE_PROVER"]
        prefix = Path(os.environ["ITPEVAL_PREFIX"]).resolve()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = Path(os.environ.get("ITPEVAL_TEST_CACHE", root / "cache"))
            prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
            profile = TaskProfile.from_lock(prepared.lock_path)
            task = profile.task
            candidate = task.allowed_edits[0]
            native = verify(task, candidate, prepared=prepared)
            self.assertIs(native.task_success, True, native.stderr)
            model = {"id": "local", "label": "local", "provider": "local"}
            with patch("eval.pipeline.completion.translate", side_effect=ConnectionError("provider unavailable")):
                outage = run(profile, model, root / "provider-outage.jsonl")
            self.assertIsNone(outage["task_success"])
            self.assertEqual(outage["evidence"]["execution_outcome"], "generation_error")
            self.assertEqual(proof_reward(task, VerificationEvidence.from_dict(outage["evidence"])).disposition,
                             "infrastructure_failure")
            sync = run(profile, model, root / "sync.jsonl", prerecorded=candidate)
            raw = root / "raw.jsonl"
            run(profile, model, raw, prerecorded=candidate, generate_only=True)
            self.assertNotIn("evidence", json.loads(raw.read_bytes()))
            posthoc = json.loads(_verify_file(raw, 1, hol_light_timeout_s=None, profile=profile,
                                             output_dir=root / "posthoc").read_bytes())
            job = root / "job.json"
            path = root / "candidate.txt"
            path.write_bytes(candidate.encode())
            settings = ["--completion-lock", str(prepared.lock_path)]
            batch_main(["submit", *settings, "--candidate", str(path), "--job-file", str(job)])
            batch_main(["collect", str(job), *settings, "--workers", "1", "--output", str(root / "batch.jsonl")])
            batch = json.loads((root / "batch.jsonl").read_bytes())
            attempts = []
            trainer = VerifierReward({task.task_id: (task, prepared)}, record=attempts.append)
            self.assertEqual(trainer([candidate], [task.task_id]), [1])
            for row in (sync, posthoc, batch, attempts[0]):
                observed = VerificationEvidence.from_dict(row["evidence"])
                self.assertEqual(proof_reward(task, observed).value, 1)
                for key in ("task_id", "environment_id", "artifact_id", "task_success",
                            "execution_outcome", "checker_outcome", "completion_status", "obligations"):
                    self.assertEqual(getattr(observed, key), getattr(native, key))
            with self.assertRaisesRegex(ValueError, "manifest mismatch"):
                run(profile, model, root / "sync.jsonl", prerecorded=task.allowed_edits[1])

            episode_file = run_episode(prover, prefix, cache, root / "episode")
            episode = Episode.from_dict(json.loads(episode_file.read_bytes()))
            self.assertTrue(replay(episode, task=task, prepared=prepared).task_success)
            self.assertEqual(export_jsonl([episode], root / "train.jsonl", view="supervised"), 1)
            repair, = repair_rows([episode])
            self.assertEqual(repair["failed_candidate"], task.allowed_edits[1])
            self.assertEqual(repair["completion"], task.allowed_edits[0])
            self.assertEqual([row["reward"] for row in trajectory_rows([episode])], [0, 1])
            first, second = episode.transitions
            replaced = replace(episode, transitions=(replace(first, action=second.action), second))
            with self.assertRaisesRegex(ValueError, "checked artifact"):
                list(trajectory_rows([replaced]))
