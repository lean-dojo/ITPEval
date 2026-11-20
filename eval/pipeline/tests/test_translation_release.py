from __future__ import annotations

import argparse
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.translation.batch_run import _make_request, cmd_collect, cmd_submit
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.run import _run_single


class TranslationReleaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pair = next(p for p in load_pairs("stmts", sources=["babel-formal"], theorem_ids=[1])
                        if p["src_prover"] == "lean4" and p["tgt_prover"] == "pvs")
        cls.model = {"id": "fixture", "label": "fixture", "provider": "fixture"}

    def run_single(self, generated):
        with patch("eval.pipeline.translation.run.translate", return_value=generated), \
             contextlib.redirect_stdout(io.StringIO()):
            return _run_single(model_cfg=self.model, pair=self.pair, sample_idx=0,
                               mode="stmts", temperature=0, max_tokens=100,
                               job_num=1, total=1)

    def test_sync_unwraps_statement_before_native_verification(self):
        code = "Target: THEORY\nBEGIN\nstatement: bool = TRUE\nEND Target\n"
        with patch("eval.pipeline.verify.run_itp", return_value=SimpleNamespace(
                ok=True, duration_ms=3, stdout="", stderr="")) as native:
            record = self.run_single("```pvs\n" + code + "```\n")
        self.assertTrue(record["verified"])
        self.assertIsNone(record["task_success"])
        self.assertEqual(record["evidence"]["completion_status"], "statement_accepted")
        self.assertEqual(record["evidence"]["target_preservation"], "unbound")
        self.assertEqual(record["generated"], code)
        self.assertEqual(record["raw_generated"], "```pvs\n" + code + "```\n")
        self.assertEqual(native.call_args.kwargs["code"], code)
        self.assertEqual(native.call_args.kwargs["timeout_s"], 300)
        self.assertEqual(record["corpus"], "extended")

    def test_invalid_statement_never_reaches_native_checker(self):
        with patch("eval.pipeline.verify.run_itp") as native:
            record = self.run_single("Target: THEORY\nBEGIN\ntarget: AXIOM TRUE\nEND Target\n")
        self.assertFalse(record["verified"])
        self.assertTrue(record["verify_error"])
        native.assert_not_called()

    def test_completed_batch_preserves_corpus_and_source_identity(self):
        request = _make_request(self.pair, "stmts")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            job = root / "job.json"
            job.write_text(json.dumps({"mode": "stmts", "requests": [request], "models": {
                "fixture": {"provider": "fixture", "model_id": "fixture", "status": "completed",
                            "batch_ids": [], "results": {request["custom_id"]: "candidate"}},
            }}))
            with patch("eval.pipeline.translation.batch_run.VERIFIED_DIR", root / "verified"), \
                 patch("eval.pipeline.translation.batch_run.verify_translation_records") as verify, \
                 contextlib.redirect_stdout(io.StringIO()):
                cmd_collect(argparse.Namespace(job_file=str(job), workers=1))
            record = verify.call_args.args[0][0]
            self.assertEqual(record["corpus"], "extended")
            self.assertEqual(record["source_sha256"], self.pair["source_sha256"])
            self.assertEqual(record["custom_id"], request["custom_id"])

    def test_batch_preview_does_not_create_jobs_or_submit(self):
        with tempfile.TemporaryDirectory() as directory:
            jobs = Path(directory) / "jobs"
            args = argparse.Namespace(mode="stmts", sources="babel-formal", ids="1",
                                      subset=None, models="gpt-5.5",
                                      src="lean4", tgt="pvs", dry_run=True)
            with patch("eval.pipeline.translation.batch_run.BATCH_JOBS_DIR", jobs), \
                 patch("eval.pipeline.translation.batch_run.submit") as submit, \
                 contextlib.redirect_stdout(io.StringIO()):
                cmd_submit(args)
            submit.assert_not_called()
            self.assertFalse(jobs.exists())


if __name__ == "__main__":
    unittest.main()
