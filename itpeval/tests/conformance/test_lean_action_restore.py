"""Check Lean tactic checkpoint restoration against the installed native server."""

from dataclasses import replace
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from unittest import TestCase, skipUnless
from unittest.mock import patch

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import LeanTacticSession
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires an installed Lean toolchain")
class LeanActionRestoreTests(TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        fixture = curated_project("lean4").parent / "action-restore"
        self.prepared = prepare_project("lean4", fixture, cache=Path(temporary.name),
                                        prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
        self.task = build_task(self.prepared)
        self.actions = tuple(map(str.strip, self.task.allowed_edits[0].splitlines()))

    def test_batch_restores_every_native_observation(self):
        driver = NativeProofDriver(self.task, self.prepared)
        expected = [driver.observe()]
        for tactic in self.actions:
            transition = driver.advance(NativeProofAction("tactic", tactic))
            self.assertTrue(transition.committed)
            expected.append(transition.observation)
        checkpoint = driver.checkpoint()
        self.assertEqual(len(set(checkpoint.state_ids)), len(expected))
        self.assertEqual(expected[-1].status, "ready")

        session = LeanTacticSession(self.task, self.prepared)
        initial = session.handle
        with patch.object(session, "_run", wraps=session._run) as run:
            rows = session.replay_prefix(initial, iter(self.actions))
            self.assertEqual(rows, tuple(state.native for state in expected))
            run.assert_called_once()
        self.assertEqual(session.handle.revision, len(self.actions))
        with self.assertRaisesRegex(ValueError, "already finished"):
            session.step(session.handle, "skip")
        with self.assertRaisesRegex(ValueError, "stale"):
            session.replay_prefix(initial, ())
        with self.assertRaisesRegex(ValueError, "unused proof session"):
            session.replay_prefix(session.handle, ())

        restored = NativeProofDriver.from_checkpoint(self.task, self.prepared, checkpoint)
        self.assertEqual(restored.checkpoint(), checkpoint)
        self.assertEqual(restored.observe(), expected[-1])
        final = restored.finalize()
        self.assertEqual(final.candidate, " <;> ".join(self.actions))
        self.assertTrue(final.evidence.task_success)
        self.assertIn("does not depend on any axioms", final.evidence.stdout)

        state_ids = (*checkpoint.state_ids[:3], "0" * 64, *checkpoint.state_ids[4:])
        with self.assertRaisesRegex(ValueError, "differed at replay step 3"):
            NativeProofDriver.from_checkpoint(self.task, self.prepared, replace(checkpoint, state_ids=state_ids))

    def test_replay_failure_and_cancellation_preserve_the_unused_session(self):
        session = LeanTacticSession(self.task, self.prepared)
        initial = session.handle
        for tactic, diagnostic in (("exact False.elim", "Type mismatch"),
                                   ("invalid_tactic", "unknown tactic")):
            with self.subTest(tactic=tactic):
                with self.assertRaisesRegex(ValueError, f"(?s)replay step 3.*{diagnostic}"):
                    session.replay_prefix(initial, (*self.actions[:2], tactic, *self.actions[2:]))
                self.assertEqual(session.handle, initial)
                self.assertIsNone(session.candidate)
        with self.assertRaisesRegex(ValueError, f"replay step {len(self.actions) + 1}.*already finished"):
            session.replay_prefix(initial, (*self.actions, "skip"))
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)

        cancelled = Event()
        cancelled.set()
        with self.assertRaisesRegex(RuntimeError, "cancelled"):
            session.replay_prefix(initial, self.actions, cancel=cancelled)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)

        cancelled.clear()
        native_run = session._run

        def cancel_after_response(*args, **kwargs):
            result = native_run(*args, **kwargs)
            cancelled.set()
            return result

        with patch.object(session, "_run", cancel_after_response):
            with self.assertRaisesRegex(RuntimeError, "cancelled"):
                session.replay_prefix(initial, self.actions, cancel=cancelled)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)

        empty = session.replay_prefix(initial, ())
        self.assertEqual(empty, (session.inspect(initial),))
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)
        start = session.replay_prefix(initial, self.actions[:2])
        handle, advanced = session.step(session.handle, self.actions[2])
        self.assertEqual(handle.revision, 3)
        self.assertEqual(advanced["before"], dict(start[-1], version=1))
