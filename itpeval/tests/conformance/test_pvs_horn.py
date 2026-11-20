"""Exercise typed native PVS sequents, external search, and strict ProofLite replay."""

import json
import os
import tempfile
import unittest
from pathlib import Path
from threading import Event

from itpeval.atp.pvs import search_pvs_horn
from itpeval.atp.search import prepare_solver
from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


FIXTURES = Path(__file__).resolve().parents[1] / "fixtures/projects/pvs"
PROOFLITE = "(then (skosimp) (split 1) (grind))"


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native PVS Horn checks")
class NativePVSHornTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def _driver(self, source, cache, *commands):
        prepared = prepare_project("pvs", source, prefix=self.prefix, cache=cache)
        driver = NativeProofDriver(build_task(prepared), prepared)
        for command in commands:
            step = driver.advance(NativeProofAction("command", command))
            self.assertTrue(step.committed)
        return driver

    def test_external_search_progress_and_strict_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory)
            driver = self._driver(FIXTURES / "horn", cache, "(skosimp)", "(split 1)")
            before = driver.checkpoint()
            for name in ("e", "vampire"):
                with self.subTest(solver=name):
                    solver = prepare_solver(name, prefix=self.prefix)
                    suggestion = driver.suggest_atp(solver=solver)
                    result = suggestion.evidence
                    self.assertEqual(suggestion.outcome, "progress")
                    self.assertEqual(result.probe["observation"]["path"], "0.0")
                    self.assertEqual(result.probe["observation"]["conclusion"]["formula"], "q!1")
                    self.assertEqual([row["label"] for row in result.probe["observation"]["premises"]], [-1, -2, -3])
                    self.assertEqual(result.probe["search"]["native_status"], "Theorem")
                    self.assertEqual(result.after.native["events"][-1]["path"], "0.1")
                    self.assertIsNone(result.finalization)
                    self.assertEqual(driver.checkpoint(), before)

                    branch = driver.fork()
                    self.assertTrue(branch.apply_atp(suggestion).committed)
                    with self.assertRaisesRegex(ValueError, "another task or proof revision"):
                        branch.apply_atp(suggestion)
                    final_suggestion = branch.suggest_atp(solver=solver, proof_fragment=PROOFLITE)
                    final = final_suggestion.evidence
                    self.assertEqual(final.outcome, "accepted")
                    self.assertEqual(final.probe["observation"]["conclusion"]["formula"], "r!1")
                    self.assertEqual(final.finalization.match, "same_locked_target")
                    self.assertEqual(dict(final.finalization.evidence.obligations),
                                     {"transitive_local": "discharged", "twice_TCC1": "discharged"})
                    self.assertTrue(branch.fork().apply_atp(final_suggestion).committed)

            no_fragment = search_pvs_horn(branch, solver=solver)
            self.assertEqual(no_fragment.outcome, "proof_fragment_required")
            self.assertIsNone(no_fragment.action)
            rejected = search_pvs_horn(branch, solver=solver, proof_fragment="(skip)")
            self.assertEqual(rejected.outcome, "incomplete")
            self.assertIsNone(rejected.action)
            self.assertFalse(rejected.trials[0].verification.task_success)

    def test_compound_goal_and_cancellation_produce_no_action(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = self._driver(FIXTURES / "grind", Path(directory), "(skosimp)", "(split)")
            solver = prepare_solver("e", prefix=self.prefix)
            before = driver.checkpoint()
            unsupported = search_pvs_horn(driver, solver=solver)
            self.assertEqual(unsupported.outcome, "unsupported_goal")
            self.assertIsNone(unsupported.action)
            self.assertNotIn("search", unsupported.probe)
            cancel = Event()
            cancel.set()
            self.assertEqual(search_pvs_horn(driver, solver=solver, cancel=cancel).outcome, "cancelled")
            self.assertEqual(driver.checkpoint(), before)

    def test_zero_premises_preserves_the_external_countermodel(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "project"
            source.mkdir()
            statement = "FORALL (p: bool): p"
            anchor = f"open_goal: LEMMA {statement}\n  %|- open_goal : PROOF\n  %|- (skip)\n  %|- QED"
            (source / "pending.pvs").write_text(f"pending: THEORY\nBEGIN\n  {anchor}\nEND pending\n", encoding="utf-8")
            manifest = {"schema_version": 1, "entrypoint": "pending.pvs", "files": ["pending.pvs"],
                        "anchor": anchor, "target": "open_goal", "statement": statement, "proof_slot": "(skip)",
                        "allowed_edits": ["(skip)"], "proof_atoms": ["(skosimp)", "(grind)"]}
            (source / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            driver = self._driver(source, root / "cache", "(skosimp)")
            solver = prepare_solver("e", prefix=self.prefix)
            result = search_pvs_horn(driver, solver=solver)
            self.assertEqual(result.outcome, "counter_satisfiable")
            self.assertEqual(result.probe["observation"]["premises"], [])
            self.assertEqual(result.probe["tptp"], "fof(goal, conjecture, p1).\n")
            self.assertEqual(result.probe["search"]["native_status"], "CounterSatisfiable")
            self.assertFalse(result.trials)
            self.assertIsNone(result.action)
