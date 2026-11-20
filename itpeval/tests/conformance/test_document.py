"""Whole-document submissions through the SDK, native CLI and revision sessions."""
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.core.types import Artifact
from itpeval.environments import prepare_project
from itpeval.runtime.sessions import DocumentSession
from itpeval.verification import verify_document
from itpeval.verification.policies import assemble


class DocumentPolicyTests(unittest.TestCase):
    def setUp(self):
        self.project = curated_project("isabelle")
        self.prepared = SimpleNamespace(project=self.project, environment_id="fixture",
                                        spec=SimpleNamespace(prover="isabelle", checking_profile="strict"),
                                        validate=lambda: None)
        self.task = build_task(self.prepared)
        self.entry = self.task.artifact.entrypoint
        self.files = {entry.path: (self.project / entry.path).read_bytes() for entry in self.task.artifact.files}

    def test_file_set_entrypoint_fixed_siblings_and_encoding(self):
        revised = [
            Artifact.from_files("ROOT", self.files),
            Artifact.from_files(self.entry, {self.entry: self.files[self.entry]}),
            Artifact.from_files(self.entry, {**self.files, "extra.thy": b""}),
            Artifact.from_files(self.entry, {**self.files, "ROOT": self.files["ROOT"] + b"\n"}),
            Artifact.from_files(self.entry, {**self.files, self.entry: self.files[self.entry] + b"\r\n"}),
        ]
        for submitted in revised:
            with self.subTest(artifact_id=submitted.artifact_id):
                ev = verify_document(self.task, submitted, prepared=self.prepared)
                self.assertEqual((ev.artifact_id, ev.target_preservation, ev.checker_outcome, ev.execution_outcome),
                                 (submitted.artifact_id, "violated", "policy_rejected", "not_run"))
                self.assertIn("submitted_artifact:" + submitted.artifact_id, ev.evidence_references)
        m = json.loads((self.project / "completion.json").read_bytes())
        source = self.files[self.entry]
        for slot, expected in [(b"\xff", "policy_rejected"), (b"", "incomplete")]:
            modified = source.replace(m["proof_slot"].encode(), slot)
            ev = verify_document(self.task, modified, prepared=self.prepared)
            self.assertEqual((ev.target_preservation, ev.checker_outcome), ("preserved", expected))

    def test_wrong_environment_is_indeterminate_even_for_changed_document(self):
        self.prepared.environment_id = "another"
        ev = verify_document(self.task, b"", prepared=self.prepared)
        self.assertIsNone(ev.task_success)
        self.assertEqual(ev.execution_outcome, "unavailable_environment")


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "set ITPEVAL_REAL_PREFIX for native document checks")
class NativeDocumentTests(unittest.TestCase):
    def test_original_and_instrumented_documents_and_rejected_finalization(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared = prepare_project("lean4", curated_project("lean4"), prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                       cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", tmp)))
            task = build_task(prepared)
            valid = task.allowed_edits[2]
            instrumented = assemble(task, valid)
            entry = task.artifact.entrypoint
            original = (prepared.project / entry).read_text().replace("  rfl\n", "  " + valid + "\n")
            self.assertIn("(x : Nat)", original)
            session = DocumentSession(task, prepared)
            handle, result = session.submit_document(session.handle, original)
            self.assertIs(result.task_success, True, result.stderr)
            self.assertEqual(result.artifact_id, instrumented.artifact_id)
            handle, result2 = session.submit_document(handle, instrumented)
            self.assertIs(result2.task_success, True, result2.stderr)
            self.assertIn("submitted_artifact:" + instrumented.artifact_id, result2.evidence_references)
            handle, failure = session.submit_document(handle, original.replace("(x : Nat)", "(x : Int)"))
            self.assertFalse(failure.task_success)
            self.assertEqual(session.finalize(handle), failure)
            repaired, result3 = session.submit(handle, valid)
            self.assertTrue(result3.task_success)
            self.assertTrue(session.finalize(repaired).task_success)
            replayed, observations = session.replay_documents([original, ""])
            self.assertEqual([item.task_success for item in observations], [True, False])
            self.assertEqual(replayed.revision, 2)
            self.assertEqual(session.finalize(replayed), observations[-1])
            with self.assertRaises(ValueError):
                session.finalize(repaired)
            self.assertEqual(session.finalize(session.reset()).checker_outcome, "incomplete")

    def test_cli_whole_source_and_artifact_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = curated_project("metamath")
            prepared = prepare_project("metamath", project, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                       cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", tmp)))
            task = build_task(prepared)
            entry = task.artifact.entrypoint
            cli = [sys.executable, "-m", "itpeval.cli", "verify-task", "--lock", str(prepared.lock_path)]
            checked = subprocess.run([*cli, "--document-file", str(project / entry)], capture_output=True, text=True, check=False)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(json.loads(checked.stdout)["completion_status"], "proved")
            bundle = Artifact.from_files(entry, {entry: b" "})
            path = Path(tmp) / "submission.json"
            path.write_text(json.dumps(bundle.to_dict()))
            rejected = subprocess.run([*cli, "--artifact-json", str(path)], capture_output=True, text=True, check=False)
            self.assertEqual(rejected.returncode, 1, rejected.stdout + rejected.stderr)
            ev = json.loads(rejected.stdout)
            self.assertEqual((ev["artifact_id"], ev["target_preservation"]), (bundle.artifact_id, "violated"))
            self.assertIn("submitted_artifact:" + bundle.artifact_id, ev["evidence_references"])
