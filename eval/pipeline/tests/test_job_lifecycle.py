import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from eval.pipeline.batch import openai_poll
from eval.pipeline.beq.beq_check import beq_verify_file
from eval.pipeline.cycle.run import run_cycle
from eval.pipeline.records import translation_custom_id
from eval.pipeline.translation.batch_run import main as batch
from eval.pipeline.translation.data import load_pairs
from itpeval.backends.registry import curated_task
from itpeval.core.episodes import Episode
from itpeval.learning.episodes import check_episode, export_jsonl, replay
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rollouts import rollout


class EvaluationLifecycleTests(unittest.TestCase):
    selection = ["--corpus", "published", "--sources", "minif2f", "--ids", "350",
                 "--src", "lean4", "--tgt", "rocq"]
    model = {"id": "sample", "label": "sample", "provider": "openai"}

    def test_archived_population_retains_original_ids(self):
        pairs = load_pairs(corpus="published")
        self.assertEqual(len(pairs), 390 * 4 * 3)
        self.assertEqual(len({(p["source"], p["theorem_id"]) for p in pairs}), 390)
        self.assertEqual(len({translation_custom_id(p) for p in pairs}), len(pairs))
        self.assertTrue(all(p["corpus"] == "published" for p in pairs))

    def test_ambiguous_submission_requires_remote_id_before_collecting(self):
        with tempfile.TemporaryDirectory() as directory:
            job = Path(directory) / "job.json"
            command = ["submit", *self.selection, "--models", "gpt-5.5", "--job-file", str(job)]
            with patch("eval.pipeline.translation.batch_run.submit", side_effect=ConnectionError("lost reply")) as submit:
                with self.assertRaises(ConnectionError):
                    batch(command)
                with self.assertRaisesRegex(ValueError, "unconfirmed"):
                    batch(command)
                self.assertEqual(submit.call_count, 1)
                with self.assertRaisesRegex(ValueError, "unconfirmed"):
                    batch([*command, "--recover-batch", "other=batch-1"])
                batch([*command, "--recover-batch", "gpt-5.5=batch-1"])
                batch(command)
                submit.assert_called_once()
            state = json.loads(job.read_bytes())
            self.assertEqual(state["models"]["gpt-5.5"]["batch_ids"], ["batch-1"])
            self.assertEqual(state["models"]["gpt-5.5"]["status"], "submitted")
            state["requests"][0]["system_prompt"] += "different"
            job.write_text(json.dumps(state))
            with self.assertRaisesRegex(ValueError, "manifest"):
                batch(["collect", str(job)])

    def test_local_submission_preserves_missing_output_and_rejects_corruption(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            job, responses = root / "job.json", root / "raw.json"
            responses.write_text("{}")
            batch(["submit", *self.selection, "--responses", str(responses), "--job-file", str(job)])
            spool, = job.with_suffix(".json.spool").glob("*.json")
            payload = spool.read_bytes()
            spool.write_text("{}")
            with self.assertRaisesRegex(ValueError, "receipt"):
                batch(["collect", str(job)])
            self.assertEqual(json.loads(job.read_bytes())["models"]["prerecorded"]["status"], "submitted")
            spool.write_bytes(payload)
            with patch("eval.pipeline.translation.batch_run.verify_translation_records") as verify:
                batch(["collect", str(job), "--output", str(root / "out.jsonl")])
            row, = verify.call_args.args[0]
            self.assertEqual(row["generated"], "")
            self.assertIn("no output", row["translate_error"])
            self.assertEqual(row["generation_run_id"], json.loads(job.read_bytes())["run_id"])

    def test_provider_partial_batch_retains_each_result(self):
        delivered = {"custom_id": "first", "response": {"body": {"choices": [{"message": {"content": "proof"}}]}}}
        failed = {"custom_id": "second", "error": {"code": "provider_error"}}
        client = Mock()
        for state in ("completed", "expired"):
            with self.subTest(state=state):
                client.batches.retrieve.return_value = SimpleNamespace(status=state, output_file_id="out", error_file_id="err")
                client.files.content.side_effect = [SimpleNamespace(content=json.dumps(r).encode()) for r in (delivered, failed)]
                with patch.dict(os.environ, {"OPENAI_API_KEY": "unused"}), patch("eval.pipeline.batch._ensure_loaded"), \
                     patch.dict(sys.modules, {"openai": SimpleNamespace(OpenAI=lambda **kw: client)}):
                    status, rows = openai_poll("saved-handle")
                self.assertEqual(status, state)
                self.assertEqual(rows["first"], "proof")
                self.assertIn("provider_error", rows["second"]["error"])

    def test_expired_job_still_exports_delivered_and_missing_rows(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            job = root / "job.json"
            conditions = ["--corpus", "published", "--sources", "minif2f", "--ids", "350,375",
                          "--src", "lean4", "--tgt", "rocq"]
            with patch("eval.pipeline.translation.batch_run.submit", return_value="expired-batch"):
                batch(["submit", *conditions, "--models", "gpt-5.5", "--job-file", str(job)])
            first, second = json.loads(job.read_bytes())["requests"]
            with patch("eval.pipeline.translation.batch_run.poll", return_value=("expired", {first["custom_id"]: "raw"})), \
                 patch("eval.pipeline.translation.batch_run.verify_translation_records") as verify:
                with self.assertRaisesRegex(SystemExit, "failed"):
                    batch(["collect", str(job), "--output", str(root / "verified.jsonl")])
            rows = {row["custom_id"]: row for row in verify.call_args.args[0]}
            self.assertEqual(rows[first["custom_id"]]["generated"], "raw")
            self.assertIn("expired", rows[second["custom_id"]]["translate_error"])
            self.assertEqual(json.loads(job.read_bytes())["models"]["gpt-5.5"]["failed_batch_ids"], ["expired-batch"])

    def test_proof_manifest_includes_the_installed_verification_policy(self):
        task = curated_task("metamath", "environment")
        with patch("itpeval.verification.cache.verifier_revision", side_effect=["first", "second"]):
            a, b = [RunManifest.for_proof_task(task, "data", "prompt", {}, max_attempts=2) for _ in range(2)]
        self.assertNotEqual(a.run_id, b.run_id)
        self.assertEqual(a.budgets["checker"], task.budgets.to_dict())

    def test_cycle_checkpoint_binds_input_model_and_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            settings = dict(cycle=1, records=[{"name": "x", "nl": "A", "split": "test"}],
                            models=[self.model], workers=1, max_tokens=8, output_dir=Path(directory))
            with patch("eval.pipeline.cycle.run._call", return_value=("text", "", 1)) as request:
                run_cycle(**settings)
                run_cycle(**settings)
                self.assertEqual(request.call_count, 3)
                for mismatch in ({"models": [{**self.model, "id": "changed"}]}, {"max_tokens": 7}):
                    with self.assertRaisesRegex(ValueError, "manifest mismatch"):
                        run_cycle(**{**settings, **mismatch})
            self.assertIn("run_id", json.loads((Path(directory) / "cycle1/sample.jsonl").read_bytes()))

    def test_archived_beq_keys_distinguish_models_and_generated_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "input.jsonl"
            rows = [{"custom_id": "same-legacy-id", "model": m, "verified": False, "tgt_prover": "rocq",
                     "theorem_id": 1, "title": "test", "generated": "input"} for m in ("first", "second")]
            src.write_text("".join(json.dumps(r) + "\n" for r in rows))
            out = beq_verify_file(src, {}, 1, output_dir=root / "results")
            checked = [json.loads(line) for line in out.read_text().splitlines()]
            self.assertEqual([r["model"] for r in checked], ["first", "second"])
            self.assertTrue(all(r["beq_status"] == "equivalence not established" for r in checked))
            src.write_text(src.read_text().replace('"input"', '"other"'))
            with self.assertRaisesRegex(ValueError, "manifest mismatch"):
                beq_verify_file(src, {}, 1, output_dir=root / "results")

    def test_generator_failure_is_retained_as_an_unscored_attempt(self):
        task = curated_task("metamath", "environment")
        prepared = SimpleNamespace(environment_id="environment", spec=SimpleNamespace(prover="metamath"))
        manifest = RunManifest((task.task_id,), (task.environment_id,), "proof_completion.v1", "data", "prompt",
                               {}, 0, {"max_attempts": 2})
        generate = Mock(side_effect=ConnectionError("provider offline"))
        with patch("itpeval.learning.rollouts.verify") as native:
            episode = rollout(task, prepared, manifest, generate)
            native.assert_not_called()
        result = check_episode(Episode.from_dict(episode.to_dict()), task)
        self.assertIsNone(result.task_success)
        self.assertEqual(result.execution_outcome, "generation_error")
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "out.jsonl"
            self.assertEqual(export_jsonl([episode], out), 1)
            self.assertIsNone(json.loads(out.read_bytes())["reward"])
            self.assertEqual(export_jsonl([episode], out, view="supervised"), 0)
            with self.assertRaisesRegex(ValueError, "no native check"):
                replay(episode, task=task, prepared=prepared)
