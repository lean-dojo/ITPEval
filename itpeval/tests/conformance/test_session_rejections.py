"""Check rejected native edits without advancing the committed proof revision."""
import json
import os
from pathlib import Path
from shutil import copytree
from tempfile import TemporaryDirectory
import unittest

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import AgdaHoleSession, LeanTacticSession


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "set ITPEVAL_REAL_PREFIX for native proof checks")
class NativeRejectionTests(unittest.TestCase):
    def _project(self, prover, fixture, key, edits):
        temp = TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        project = root / "project"
        copytree(fixture, project)
        manifest = project / "completion.json"
        contents = json.loads(manifest.read_text(encoding="utf-8"))
        contents[key].extend(edits)
        manifest.write_text(json.dumps(contents), encoding="utf-8")
        return prepare_project(prover, project, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                               cache=root / "cache")

    def test_lean_keeps_the_last_valid_revision_after_an_elaboration_error(self):
        prepared = self._project("lean4", curated_project("lean4"), "proof_atoms",
                                 ["skip", "exact False.elim", "invalid_tactic"])
        session = LeanTacticSession(build_task(prepared), prepared)
        initial = session.handle
        same, rejected = session.step(initial, "exact False.elim")
        self.assertEqual(same, initial)
        self.assertIsNone(session.candidate)
        self.assertTrue(any("Type mismatch" in row["message"] for row in rejected["after"]["diagnostics"]))

        partial, observed = session.step(initial, "skip")
        self.assertNotEqual(partial, initial)
        self.assertTrue(observed["after"]["goal"]["goals"])
        self.assertTrue(any(1 in row.get("leanTags", []) for row in observed["after"]["diagnostics"]))
        for tactic in ("exact False.elim", "invalid_tactic"):
            with self.subTest(tactic=tactic):
                same, rejected = session.step(partial, tactic)
                self.assertEqual(same, partial)
                self.assertEqual(session.candidate, "skip")
                self.assertEqual(session.inspect(same)["goal"], observed["after"]["goal"])
                self.assertTrue(any(row.get("severity") == 1 for row in rejected["after"]["diagnostics"]))

        complete, observed = session.step(partial, "rfl")
        self.assertFalse(observed["after"]["goal"]["goals"])
        self.assertTrue(session.finalize(complete).task_success)
        with self.assertRaisesRegex(ValueError, "already finished"):
            session.step(complete, "rfl")
        with self.assertRaisesRegex(ValueError, "stale"):
            session.inspect(partial)

    def test_agda_keeps_the_hole_after_type_errors_or_invisible_metas(self):
        fixture = curated_project("agda").parent / "interaction"
        prepared = self._project("agda", fixture, "allowed_edits", ["= _"])
        session = AgdaHoleSession(build_task(prepared), prepared)
        initial = session.handle
        goal = session.goal_context(initial)
        same, error = session.give(initial, "Bool")
        self.assertEqual(same, initial)
        self.assertTrue(any(event["kind"] == "DisplayInfo" and event["info"]["kind"] == "Error" for event in error))
        self.assertEqual(session.goal_context(same), goal)

        same, incomplete = session.give(same, "_")
        self.assertEqual(same, initial)
        self.assertTrue(any(event["kind"] == "GiveAction" for event in incomplete))
        summaries = [event["info"] for event in incomplete
                     if event["kind"] == "DisplayInfo" and event["info"]["kind"] == "AllGoalsWarnings"]
        self.assertFalse(summaries[-1]["visibleGoals"])
        self.assertTrue(summaries[-1]["invisibleGoals"])
        self.assertIsNone(session.candidate)
        self.assertEqual(session.goal_context(same), goal)

        complete, _ = session.give(same, "x")
        self.assertNotEqual(complete, initial)
        events = session.inspect(complete)
        self.assertFalse([row["interactionPoints"] for row in events if row["kind"] == "InteractionPoints"][-1])
        self.assertTrue(session.finalize(complete).task_success)
        with self.assertRaisesRegex(ValueError, "already been filled"):
            session.goal_context(complete)
        with self.assertRaisesRegex(ValueError, "stale"):
            session.goal_context(initial)
