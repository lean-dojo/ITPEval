"""Exercise the typed adapter contract with Sprig outside the package tree."""

import json
import os
from pathlib import Path
from shutil import copy2, copytree, ignore_patterns
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from itpeval.backends.registry import get_backend, project_prover_ids, prover_ids
from itpeval.core.episodes import Action
from itpeval.core.types import Artifact, TaskSpec
from itpeval.corpus.datasets import export_dataset, match_target
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import load_project, prepare_project
from itpeval.learning.episodes import check_episode, replay, task_prompt
from itpeval.learning.example import completion_row
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rewards import proof_reward
from itpeval.learning.rollouts import rollout
from itpeval.runtime.scheduler import Job, run_jobs
from itpeval.runtime.sessions import DocumentCheckpoint, DocumentSession
from itpeval.verification import candidate_from_bytes, verify, verify_document
from itpeval.verification.cache import verify_cached


SPRIG = Path(__file__).resolve().parents[3] / "examples/prover-adapters/sprig"
DRAT = SPRIG.parent / "drat"


@unittest.skipUnless(SPRIG.is_dir(), "Sprig source is needed for the out-of-tree adapter example")
class ExternalAdapterTests(unittest.TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.adapter = self.root / "adapters/sprig"
        copytree(SPRIG, self.adapter, ignore=ignore_patterns("__pycache__"))
        configure = patch.dict(os.environ, {"ITPEVAL_ADAPTER_DIR": str(self.adapter.parent)})
        configure.start()
        self.addCleanup(configure.stop)

    def prepare(self):
        return prepare_project("sprig", self.adapter / "hello", prefix=self.root / "prefix", cache=self.root / "cache")

    def candidate(self):
        return (self.adapter / "hello/proof.json").read_text()

    def test_verification_checkpoint_episode_and_extraction(self):
        env = self.prepare()
        self.assertIn("sprig", project_prover_ids())
        self.assertNotIn("sprig", prover_ids())
        backend = get_backend("sprig")
        task = backend.build_task(load_project(env.lock_path))
        self.assertEqual(TaskSpec.from_dict(task.to_dict()), task)
        self.assertIn('problem.json', task_prompt(task))
        self.assertEqual(task.artifact.entrypoint, "proof.json")
        good, bad = self.candidate(), '{"steps":[],"conclusion":0}'
        session = backend.open_document(task, prepared=env)
        handle, accepted = session.submit(session.handle, good)
        self.assertTrue(accepted.task_success)
        self.assertEqual(accepted.obligations, (("goal", "discharged"),))
        fork = session.fork(handle)
        _, rejected = fork.submit_document(fork.handle, bad)
        self.assertEqual(rejected.checker_outcome, "rejected")
        saved = DocumentCheckpoint.from_dict(session.checkpoint(handle).to_dict())
        _, restored = DocumentSession.from_checkpoint(task, env, saved)
        self.assertEqual(restored.artifact_id, accepted.artifact_id)
        self.assertTrue(restored.task_success)

        files = {entry.path: entry.data for entry in task.artifact.files}
        files["problem.json"] = b'{"premises":[],"goal":[]}'
        files["proof.json"] = good.encode()
        changed = Artifact.from_files("proof.json", files)
        self.assertEqual(verify_document(task, changed, prepared=env).target_preservation, "violated")

        manifest = RunManifest.for_proof_task(task, "example", "sprig", {"id": "script"}, max_attempts=2)
        episode = rollout(task, env, manifest, lambda _, history: Action("edit_document", "", good if history else bad))
        self.assertTrue(check_episode(episode, task).task_success)
        self.assertTrue(replay(episode, task=task, prepared=env).task_success)
        batch = dict(run_jobs([Job(task, bad, env), Job(task, good, env)], workers=2))
        self.assertEqual([batch[index].checker_outcome for index in range(2)], ["rejected", "accepted"])

        bundle, premises = export_dataset(env, "problem.json", self.root / "export")
        target = match_target(bundle.path, task, prepared=env)
        self.assertEqual(target.name, "goal")
        self.assertEqual(target.checking_status, "proof_verified")
        self.assertEqual(completion_row(env, self.root / "data")["target"], target.to_dict())
        row = next(row for row in read_jsonl(premises) if row["declaration"]["name"] == "goal")
        self.assertEqual([edge["target_name"] for edge in row["proof_used"]], ["premise_0", "premise_1", "premise_2"])

    def test_changed_checker_and_removed_opt_in_block_replay_and_cache(self):
        env = self.prepare()
        task = get_backend("sprig").build_task(env)
        cache = self.root / "results"
        self.assertTrue(verify_cached(task, self.candidate(), prepared=env, cache=cache).evidence.task_success)
        self.assertTrue(verify_cached(task, self.candidate(), prepared=env, cache=cache).cache_hit)
        with patch.dict(os.environ, {"ITPEVAL_ADAPTER_DIR": str(self.root / "absent")}):
            with self.assertRaisesRegex(ValueError, "configure its typed adapter"):
                load_project(env.lock_path)
            self.assertEqual(verify(task, self.candidate(), prepared=env).execution_outcome, "unavailable_environment")
        with (self.adapter / "kernel.py").open("a", encoding="utf-8") as stream:
            stream.write("\n# Changed checker dependency\n")
        result = verify_cached(task, self.candidate(), prepared=env, cache=cache)
        self.assertFalse(result.cache_hit)
        self.assertEqual(result.evidence.execution_outcome, "unavailable_environment")

    def test_checker_must_bind_the_target_and_assumptions(self):
        path = self.adapter / "hello/completion.json"
        manifest = json.loads(path.read_bytes())
        manifest["allowed_assumptions"].pop()
        path.write_text(json.dumps(manifest), encoding="utf-8")
        env = self.prepare()
        task = get_backend("sprig").build_task(env)
        evidence = verify(task, self.candidate(), prepared=env)
        self.assertEqual(evidence.checker_outcome, "policy_rejected")
        self.assertIn("Unauthorized premises: premise_2", evidence.stderr)
        self.assertEqual(proof_reward(task, evidence).value, 0.0)

        checker = self.adapter / "verify.py"
        checker.write_text('print("accepted")\n', encoding="utf-8")
        env = self.prepare()
        task = get_backend("sprig").build_task(env)
        evidence = verify(task, self.candidate(), prepared=env)
        self.assertIsNone(evidence.task_success)
        self.assertEqual(evidence.checker_outcome, "insufficient_evidence")

    def test_extract_an_unproved_goal_and_check_an_escaped_source_anchor(self):
        reference = self.candidate()
        project = self.adapter / "hello"
        source = project / "problem.json"
        source.write_bytes(source.read_bytes().replace(b'"goal"', rb'"g\u006fal"'))
        path = project / "completion.json"
        manifest = json.loads(path.read_bytes())
        manifest["anchor"] = manifest["anchor"].replace('"goal"', r'"g\u006fal"')
        path.write_text(json.dumps(manifest), encoding="utf-8")
        (project / "proof.json").write_text("", encoding="utf-8")

        env = self.prepare()
        task = get_backend("sprig").build_task(env)
        row = completion_row(env, self.root / "data")
        self.assertEqual(row["target"]["checking_status"], "unverified")
        self.assertEqual(row["extraction_fields"]["proof_used_premises"], "unavailable")
        self.assertTrue(verify(task, reference, prepared=env).task_success)


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_DRAT") and DRAT.is_dir(),
                     "point ITPEVAL_REAL_DRAT at the native DRAT-trim executable")
class NativeCertificateTests(unittest.TestCase):
    def test_drat_text_binary_rejection_and_checkpoint(self):
        from itpeval.verification.policies import assemble

        with TemporaryDirectory() as temporary:
            work = Path(temporary)
            adapter = work / "adapters/drat"
            copytree(DRAT, adapter)
            binary = adapter / "bin/drat-trim"
            binary.parent.mkdir()
            copy2(os.environ["ITPEVAL_REAL_DRAT"], binary)
            with patch.dict(os.environ, {"ITPEVAL_ADAPTER_DIR": str(adapter.parent)}):
                env = prepare_project("drat", adapter / "hello", prefix=work, cache=work / "cache")
                backend = get_backend("drat")
                text = backend.build_task(env, "text-completion.json")
                self.assertEqual(text.candidate_format, "text_certificate")
                # Preserve the certificate's original bytes, including CRLF.
                text_proof = b"64 0\r\n0\r\n"
                text_candidate = candidate_from_bytes(text, text_proof)
                self.assertTrue(verify(text, text_candidate, prepared=env).task_success)
                self.assertEqual(assemble(text, text_candidate).files[-1].data, text_proof)

                task = backend.build_task(env)
                self.assertEqual(task.candidate_format, "binary_certificate")
                certificate = b"a\x80\x01\x00a\x00"
                with self.assertRaises(UnicodeDecodeError):
                    certificate.decode("utf-8")
                candidate = candidate_from_bytes(task, certificate)
                accepted = verify(task, candidate, prepared=env)
                self.assertTrue(accepted.task_success)
                self.assertEqual(assemble(task, candidate).files[-1].data, certificate)
                self.assertEqual(verify(task, candidate + "\n", prepared=env).checker_outcome, "policy_rejected")
                rejected = verify_document(task, b"a\x00", prepared=env)
                self.assertEqual(rejected.checker_outcome, "rejected")
                session = backend.open_document(task, prepared=env)
                handle, checked = session.submit_document(session.handle, certificate)
                checkpoint = DocumentCheckpoint.from_dict(session.checkpoint(handle).to_dict())
                _, replayed = DocumentSession.from_checkpoint(task, env, checkpoint)
                self.assertTrue(replayed.task_success)
                self.assertEqual(checked.artifact_id, accepted.artifact_id)
                self.assertEqual(replayed.artifact_id, accepted.artifact_id)
                manifest = RunManifest.for_proof_task(task, "drat", "binary", {"id": "fixture"}, max_attempts=2)
                incomplete = candidate_from_bytes(task, b"a\x00")
                episode = rollout(task, env, manifest, lambda _, history: Action(
                    "edit_document", "", candidate if history else incomplete))
                self.assertEqual([step.observation.task_success for step in episode.transitions], [False, True])
                self.assertTrue(replay(episode, task=task, prepared=env).task_success)

                # Reprepare with the native binary certificate as the reference
                # proof so extraction must also take the byte-preserving route.
                (adapter / "hello/proof.drat").write_bytes(certificate)
                env = prepare_project("drat", adapter / "hello", prefix=work, cache=work / "cache")
                task = backend.build_task(env)
                bundle, premises = export_dataset(env, "problem.cnf", work / "dataset")
                target = match_target(bundle.path, task, prepared=env)
                self.assertEqual(target.checking_status, "proof_verified")
                rows = list(read_jsonl(premises))
                self.assertEqual(rows[-1]["proof_used"][0]["target_name"], "input_cnf")
