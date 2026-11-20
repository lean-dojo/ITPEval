"""Check that initial Isabelle observations belong to the locked declaration."""

import json
import os
import tempfile
import unittest
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/isabelle/hammer"
FAILING_PROOF = "by (rule FalseE)"


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native Isabelle checks")
class NativeIsabelleObservationTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def _driver(self, directory, *, starter="by simp", statement=None):
        root = Path(directory)
        project = root / "project"
        project.mkdir()
        source = (FIXTURE / "HammerDemo.thy").read_text(encoding="utf-8")
        manifest = json.loads((FIXTURE / "completion.json").read_bytes())
        manifest["allowed_edits"].insert(0, FAILING_PROOF)
        reference = manifest["proof_slot"]
        source = source.replace(reference, starter)
        manifest["anchor"] = manifest["anchor"].replace(reference, starter)
        manifest["proof_slot"] = starter
        if statement is not None:
            old_statement = manifest["statement"]
            source = source.replace(old_statement, statement)
            manifest["anchor"] = manifest["anchor"].replace(old_statement, statement)
            manifest["statement"] = statement
        (project / "HammerDemo.thy").write_text(source, encoding="utf-8")
        (project / "ROOT").write_bytes((FIXTURE / "ROOT").read_bytes())
        (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
        prepared = prepare_project("isabelle", project, prefix=self.prefix, cache=root / "cache")
        return NativeProofDriver(build_task(prepared), prepared)

    def test_initial_observation_uses_locked_source_before_allowed_candidates(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = self._driver(directory)
            observation = driver.observe()
            self.assertEqual(observation.status, "open")
            self.assertTrue(observation.native["theory_checked"])
            self.assertEqual(observation.native["goals"][0]["subgoal_count"], 1)

    def test_initial_goal_survives_a_later_proof_failure_and_can_be_repaired(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = self._driver(directory, starter=FAILING_PROOF)
            observation = driver.observe()
            self.assertEqual(observation.status, "open")
            self.assertFalse(observation.native["theory_checked"])
            self.assertIn("Failed to finish proof", observation.native["diagnostic"])
            self.assertEqual(observation.native["goals"][0]["subgoal_count"], 1)

            rejected = driver.advance(NativeProofAction("edit_document", FAILING_PROOF))
            self.assertFalse(rejected.committed)
            self.assertEqual(driver.observe(), observation)

            suggestion = driver.suggest_atp(solver="e", timeout_s=30)
            self.assertEqual(suggestion.outcome, "accepted")
            changed = driver.apply_atp(suggestion)
            self.assertTrue(changed.committed)
            self.assertEqual(changed.observation.status, "ready")
            checked = driver.finalize()
            self.assertTrue(checked.evidence.task_success)
            self.assertEqual(dict(checked.evidence.obligations), {"reverse_append_probe": "discharged"})

    def test_ill_typed_declaration_does_not_open_a_goal(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = self._driver(directory, statement="True True")
            with self.assertRaisesRegex(ValueError, "prepared slot"):
                driver.observe()
