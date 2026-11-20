"""Exercise reviewed PVS strategy trials and independent ProofLite checking."""

import json
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from threading import Event

from itpeval.backends.projects import build_task
from itpeval.backends.pvs.interaction import PVSProofSession, PVSReplayFailure, review_pvs_automation
from itpeval.environments import prepare_project


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/pvs/grind"
PROOFLITE = "(then (skosimp) (split) (grind))"


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native PVS checks")
class NativePVSAutomationTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def _split(self, cache):
        prepared = prepare_project("pvs", FIXTURE, prefix=self.prefix, cache=cache)
        task = build_task(prepared)
        session = PVSProofSession(task, prepared)
        _, introduced, split = session.replay_prefix(session.handle, ("(skosimp)", "(split)"))
        return task, session, introduced, split

    def test_grind_advances_a_split_and_prooflite_checks_the_target_and_tcc(self):
        with tempfile.TemporaryDirectory() as directory:
            task, session, introduced, split = self._split(Path(directory))
            self.assertEqual([formula.text for formula in introduced.focused.sequent.antecedents], ["n!1 >= 0"])
            self.assertEqual(split.focused.path, "0.0")
            before = session.checkpoint(session.handle)
            fragment = review_pvs_automation(task, "(grind)", proof_fragment=PROOFLITE)
            branch = session.fork(session.handle)

            handle, remaining = branch.step(branch.handle, "(grind)", timeout_s=15)
            self.assertEqual(remaining.status, "waiting")
            self.assertEqual(remaining.focused.path, "0.1")
            self.assertEqual([formula.text for formula in remaining.focused.sequent.succedents],
                             ["twice(n!1) + 1 > 0"])
            self.assertEqual(session.checkpoint(session.handle), before)
            handle, done = branch.step(handle, "(grind)", timeout_s=15)
            self.assertEqual(done.status, "proved")
            with self.assertRaisesRegex(ValueError, "approved ProofLite fragment"):
                branch.finalize(handle)

            final = branch.finalize(handle, fragment)
            self.assertEqual(final.match, "same_locked_target")
            self.assertTrue(final.task_success)
            self.assertEqual(dict(final.verification.obligations),
                             {"nonnegative_twice": "discharged", "twice_TCC1": "discharged"})
            incomplete = branch.finalize(handle, "(skip)")
            self.assertFalse(incomplete.task_success)
            self.assertEqual(incomplete.verification.checker_outcome, "incomplete")

    def test_review_and_cancel_leave_the_committed_state_intact(self):
        with tempfile.TemporaryDirectory() as directory:
            task, session, _, _ = self._split(Path(directory))
            handle = session.handle
            checkpoint = session.checkpoint(handle)
            without_assert = replace(task, proof_atoms=tuple(atom for atom in task.proof_atoms if atom != "(assert)"))
            with self.assertRaisesRegex(ValueError, "automation strategy is outside the task policy"):
                review_pvs_automation(without_assert, "(assert)")
            with self.assertRaisesRegex(ValueError, "outside the task's allowed proof fragments"):
                review_pvs_automation(task, "(grind)", proof_fragment="(postpone)")
            self.assertIsNone(review_pvs_automation(task, "(assert)"))
            cancel = Event()
            cancel.set()
            with self.assertRaises(PVSReplayFailure) as outcome:
                session.step(handle, "(assert)", cancel=cancel, timeout_s=15)
            self.assertEqual(outcome.exception.outcome, "cancelled")
            with self.assertRaises(PVSReplayFailure) as outcome:
                session.step(handle, "(assert)", timeout_s=.001)
            self.assertEqual(outcome.exception.outcome, "timeout")
            self.assertEqual(session.checkpoint(handle), checkpoint)

    def test_reviewed_assert_can_leave_a_goal_open(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "project"
            source.mkdir()
            statement = "FORALL (p: bool): p"
            anchor = f"open_goal: LEMMA {statement}\n  %|- open_goal : PROOF\n  %|- (skip)\n  %|- QED"
            (source / "pending.pvs").write_text(f"pending: THEORY\nBEGIN\n  {anchor}\nEND pending\n", encoding="utf-8")
            manifest = {"schema_version": 1, "entrypoint": "pending.pvs", "files": ["pending.pvs"],
                        "anchor": anchor, "target": "open_goal", "statement": statement, "proof_slot": "(skip)",
                        "allowed_edits": ["(skip)"], "proof_atoms": ["(skosimp)", "(assert)"]}
            (source / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            prepared = prepare_project("pvs", source, prefix=self.prefix, cache=root / "cache")
            task = build_task(prepared)
            review_pvs_automation(task, "(assert)")
            session = PVSProofSession(task, prepared)
            handle, before = session.step(session.handle, "(skosimp)")
            _, attempted = session.step(handle, "(assert)", timeout_s=15)
            self.assertEqual(attempted.status, "waiting")
            self.assertIsNone(attempted.error)
            self.assertEqual(attempted.focused.sequent, before.focused.sequent)
