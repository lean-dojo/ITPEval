"""Check independent native continuations from committed Lean and Rocq states."""

from copy import deepcopy
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from unittest import TestCase, skipUnless
from unittest.mock import patch

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.backends.rocq.interaction import RocqIDESession
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import LeanTacticSession
from itpeval.verification.policies import assemble


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed Lean and Rocq toolchains")
class LeanRocqForkTests(TestCase):
    def session(self, kind, prover, fixture):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        prepared = prepare_project(prover, fixture, cache=Path(temporary.name),
                                   prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
        return kind(build_task(prepared), prepared)

    def assert_verified(self, session):
        verdict = session.finalize(session.handle)
        self.assertTrue(verdict.task_success)
        self.assertEqual(verdict.completion_status, "proved")
        self.assertEqual(verdict.target_preservation, "preserved")
        self.assertEqual(verdict.artifact_id, assemble(session.task, session.candidate).artifact_id)

    def test_lean_forks_a_native_tactic_prefix(self):
        fixture = curated_project("lean4").parent / "action-restore"
        parent = self.session(LeanTacticSession, "lean4", fixture)
        *prefix, final_tactic = map(str.strip, parent.task.allowed_edits[0].splitlines())
        initial = parent.handle
        rows = parent.replay_prefix(initial, prefix)
        anchor = parent.handle
        expected = deepcopy(dict(rows[-1], version=1))
        rows[-1]["goal"]["goals"].clear()

        with patch.object(LeanTacticSession, "_run", side_effect=AssertionError("unexpected native replay")):
            child = parent.fork(anchor)
            sibling = parent.fork(anchor)
            self.assertEqual(child.handle.revision, anchor.revision)
            self.assertNotEqual(child.handle, anchor)
            self.assertEqual(child.candidate, parent.candidate)
            child.inspect(child.handle)["diagnostics"].clear()
            for branch in (child, sibling, parent):
                self.assertEqual(branch.inspect(branch.handle), expected)
            with self.assertRaisesRegex(ValueError, "stale or foreign"):
                parent.fork(initial)
            with self.assertRaisesRegex(ValueError, "stale or foreign"):
                child.fork(anchor)

        old_child = child.handle
        closed, feedback = child.step(old_child, final_tactic)
        self.assertEqual(feedback["before"], expected)
        self.assertFalse(feedback["after"]["goal"]["goals"])
        self.assertEqual(closed.revision, old_child.revision + 1)
        self.assert_verified(child)
        self.assertEqual(parent.handle, anchor)
        self.assertEqual(parent.inspect(anchor), expected)
        self.assertEqual(sibling.inspect(sibling.handle), expected)
        self.assertNotEqual(child.candidate, parent.candidate)
        with self.assertRaisesRegex(ValueError, "stale or foreign"):
            child.fork(old_child)
        closed_fork = child.fork(closed)
        with self.assertRaisesRegex(ValueError, "already finished"):
            closed_fork.step(closed_fork.handle, final_tactic)
        cancelled = Event()
        cancelled.set()
        with self.assertRaisesRegex(RuntimeError, "cancelled"):
            parent.inspect(anchor, cancel=cancelled)
        path = parent.prepared.project / parent.task.artifact.entrypoint
        path.chmod(0o644)
        with path.open("ab") as source:
            source.write(b"\n-- changed after preparation\n")
        path.chmod(0o444)
        with self.assertRaisesRegex(ValueError, "prepared project content differs from the lock"):
            parent.inspect(anchor)

    def test_rocq_forks_native_commands_and_keeps_its_parser_spans(self):
        parent = self.session(RocqIDESession, "rocq", curated_project("rocq"))
        initial = parent.handle
        anchor, advanced = parent.step(initial, "intro p.")
        expected = deepcopy(advanced)
        advanced.goals.clear()

        with patch.object(RocqIDESession, "_run", side_effect=AssertionError("unexpected native replay")):
            child = parent.fork(anchor)
            sibling = parent.fork(anchor)
            self.assertEqual(child.handle.revision, anchor.revision)
            self.assertNotEqual(child.handle, anchor)
            self.assertEqual(child.candidate, parent.candidate)
            self.assertTrue(parent._spans)
            self.assertEqual(child._spans, parent._spans)
            self.assertIsNot(child._spans[0], parent._spans[0])
            child.inspect(child.handle).goals.clear()
            for branch in (child, sibling, parent):
                self.assertEqual(branch.inspect(branch.handle), expected)
            with self.assertRaisesRegex(ValueError, "stale or foreign"):
                parent.fork(initial)
            with self.assertRaisesRegex(ValueError, "stale or foreign"):
                child.fork(anchor)

        old_child = child.handle
        closed, state = child.step(old_child, "exact p.")
        self.assertTrue(state.complete)
        self.assertEqual(closed.revision, old_child.revision + 1)
        same, rejected = sibling.step(sibling.handle, "exact I.")
        self.assertEqual(same.revision, anchor.revision)
        self.assertTrue(rejected.error)
        self.assertEqual(sibling.inspect(same), expected)
        self.assert_verified(child)
        self.assertEqual(parent.handle, anchor)
        self.assertEqual(parent.inspect(anchor), expected)
        self.assertNotEqual(child.candidate, parent.candidate)
        with self.assertRaisesRegex(ValueError, "stale or foreign"):
            child.fork(old_child)
        child.reset()
        self.assertEqual(parent._history, ["intro p."])
