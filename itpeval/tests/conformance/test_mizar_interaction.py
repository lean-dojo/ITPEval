"""Native attachment, revision and replay checks for the reviewed Mizar article."""

import json
import os
from pathlib import Path
from shutil import copyfile
from tempfile import TemporaryDirectory
from threading import Event
from unittest import TestCase, skipUnless
from unittest.mock import patch

from itpeval.backends.mizar import diagnostics
from itpeval.backends.mizar.interaction import MizarArticleSession, MizarArticleState
from itpeval.backends.projects import CompletionManifest, build_task
from itpeval.backends.registry import curated_project
from itpeval.corpus.storage import digest
from itpeval.environments import prepare_project
from itpeval.runtime.sessions import DocumentCheckpoint
from itpeval.verification.policies import assemble


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed Mizar")
class MizarArticleSessionTests(TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.prefix = Path(os.environ["ITPEVAL_REAL_PREFIX"])
        self.prepared = prepare_project("mizar", curated_project("mizar"),
                                        prefix=self.prefix, cache=self.root / "cache")
        self.task = build_task(self.prepared)

    def test_open_closed_and_rejected_revisions_use_native_coordinates(self):
        task = self.task
        session = MizarArticleSession(task, self.prepared)
        initial_handle = session.handle
        good, wrong = task.allowed_edits[:2]
        with patch.object(diagnostics, "run_process", wraps=diagnostics.run_process) as native:
            initial = session.inspect(initial_handle)
            self.assertEqual(initial.status, "open")
            self.assertEqual([thesis.formula_kind for thesis in initial.theses], ["For", "Pred"])
            self.assertEqual((initial.trace.source_path, initial.trace.target_line, initial.trace.target_column),
                             ("hello.miz", 5, 7))
            self.assertIsNone(session.candidate)
            self.assertEqual(native.call_count, 2)

            branch = session.fork(initial_handle)
            self.assertIs(branch.inspect(branch.handle), initial)
            self.assertEqual(native.call_count, 2)
            wrong_handle, rejected = branch.step(branch.handle, wrong)
            self.assertEqual(rejected.status, "rejected")
            self.assertEqual([(d.line, d.column, d.error_code) for d in rejected.diagnostics], [(9, 20, 51), (9, 20, 1)])
            self.assertEqual(branch.candidate, wrong)
            self.assertEqual(native.call_count, 4)

            article = assemble(task, good)
            handle, proved = session.submit_document(initial_handle, article)
            source = next(file for file in article.files if file.path == article.entrypoint).data
            self.assertEqual(proved.trace.source_sha256, digest(source))
            self.assertEqual(proved.status, "closed")
            self.assertEqual(proved.theses[-1].formula_kind, "Verum")
            self.assertEqual(proved.diagnostics, ())
            self.assertEqual(session.candidate, good)
            self.assertEqual(MizarArticleState.from_dict(proved.to_dict()), proved)
            self.assertIs(session.inspect(handle), proved)
            self.assertEqual(native.call_count, 6)
            with self.assertRaisesRegex(ValueError, "stale or foreign"):
                session.step(initial_handle, good)

            checkpoint = DocumentCheckpoint.from_dict(session.checkpoint(handle).to_dict())
            restored, restored_state = MizarArticleSession.from_checkpoint(task, self.prepared, checkpoint)
            self.assertEqual(restored.candidate, good)
            self.assertEqual(restored_state.trace.source_sha256, proved.trace.source_sha256)
            self.assertEqual(native.call_count, 8)
            self.assertIs(session.finalize(handle).task_success, True)
            self.assertIs(branch.finalize(wrong_handle).task_success, False)
            self.assertEqual(native.call_count, 8)

    def test_fixed_document_and_cancelled_edit_remain_available_to_session_policy(self):
        task = self.task
        session = MizarArticleSession(task, self.prepared)
        good = task.allowed_edits[0]
        with patch.object(diagnostics, "run_process", wraps=diagnostics.run_process) as native:
            handle, changed = session.submit_document(session.handle, "environ\n\nbegin\n")
            self.assertEqual(changed.status, "rejected")
            self.assertIsNone(changed.trace)
            self.assertIsNone(session.candidate)
            self.assertEqual(session.finalize(handle).target_preservation, "violated")

            cancel = Event()
            cancel.set()
            handle, cancelled = session.step(handle, good, cancel=cancel)
            self.assertEqual(cancelled.status, "cancelled")
            self.assertEqual(session.candidate, good)
            self.assertEqual(native.call_count, 0)
            self.assertEqual(session.inspect(handle).status, "closed")
            self.assertEqual(native.call_count, 2)

        reset = session.reset()
        self.assertIsNone(session.candidate)
        self.assertEqual(session.finalize(reset).completion_status, "incomplete")

    def test_direct_justification_observes_the_named_library_proposition(self):
        project = self.root / "article"
        project.mkdir()
        copyfile(curated_project("mizar").parent / "library/sample.miz", project / "sample.miz")
        statement = "for x being object holds x = x"
        candidate = "by Th1"
        manifest = CompletionManifest("sample.miz", ("sample.miz",), f"theorem Th2: {statement} {candidate};",
                                      "Th2", statement, candidate, (candidate,))
        (project / "completion.json").write_text(json.dumps(manifest.to_dict()), encoding="utf-8")
        prepared = prepare_project("mizar", project, prefix=self.prefix, cache=self.root / "cache")
        task = build_task(prepared)
        session = MizarArticleSession(task, prepared)
        opened = session.inspect(session.handle)
        self.assertEqual(opened.status, "open")
        self.assertEqual([(thesis.kind, thesis.formula_kind) for thesis in opened.theses], [("Proposition", "For")])
        self.assertEqual((opened.trace.target_line, opened.trace.target_column), (20, 7))
        handle, closed = session.step(session.handle, candidate)
        self.assertEqual(closed.status, "closed")
        self.assertIs(session.finalize(handle).task_success, True)
