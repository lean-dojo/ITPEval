"""Exercise Agda Auto on open, source-bound goals using the installed frontend."""

import json
import os
from pathlib import Path
from shutil import copytree
from tempfile import TemporaryDirectory
from threading import Event
from unittest import TestCase, skipUnless

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import AgdaAutoDiagnostic, AgdaAutoResult, AgdaHoleSession
from itpeval.runtime.proof_driver import NativeProofDriver


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires an installed Agda toolchain")
class NativeAgdaAutoTests(TestCase):
    fixture = curated_project("agda").parent / "auto"

    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def session(self, manifest="completion.json", project=None):
        prepared = prepare_project("agda", project or self.fixture, cache=self.root / "cache",
                                   prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
        return AgdaHoleSession(build_task(prepared, manifest), prepared)

    def test_suggests_a_composed_term_and_only_give_advances_the_revision(self):
        session = self.session()
        initial = session.handle
        before = session.goal_context(initial)
        refused, _ = session.give(initial, "x")
        self.assertEqual(refused, initial)

        result = session.auto(initial)
        self.assertEqual(result.status, "candidate")
        self.assertEqual(result.candidate, "f (g x)")
        self.assertEqual(result.goal, before)
        self.assertEqual(result.goal.expected_type, "C")
        scope = {item.name: item.term for item in result.goal.bindings if item.in_scope}
        self.assertEqual({name: scope[name] for name in ("f", "g", "x")}, {"f": "B → C", "g": "A → B", "x": "A"})
        self.assertEqual(AgdaAutoResult.from_dict(result.to_dict()), result)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)
        self.assertEqual(session.goal_context(initial), before)
        handle, events = session.give(initial, result.candidate)
        self.assertEqual(handle.revision, 1)
        self.assertTrue(session._filled(events))
        self.assertEqual(session.candidate, "= f (g x)")
        proof = session.finalize(handle)
        self.assertTrue(proof.task_success)
        self.assertEqual(proof.obligations, (("compose", "discharged"),))
        with self.assertRaisesRegex(ValueError, "already been filled"):
            session.auto(handle)
        with self.assertRaisesRegex(ValueError, "stale"):
            session.auto(initial)

    def test_reports_no_result_native_errors_and_named_hints(self):
        session = self.session("right-zero.json")
        initial = session.handle
        unresolved = session.auto(initial, timeout_s=0.5)
        self.assertEqual(unresolved.status, "no_result")
        self.assertEqual(unresolved.goal.expected_type, "n + 0 ≡ n")
        self.assertEqual(unresolved.timeout_s, 0.5)
        self.assertIsNone(unresolved.candidate)
        self.assertIn(AgdaAutoDiagnostic("auto", "No solution found"), unresolved.diagnostics)
        rejected = session.auto(initial, hints=("NotAHint",))
        self.assertEqual(rejected.status, "error")
        self.assertIsNone(rejected.candidate)
        self.assertTrue(any(item.kind == "error" and "NotInScope" in item.message for item in rejected.diagnostics))
        result = session.auto(initial, hints=("plus-zero",), timeout_s=0.5)
        self.assertEqual(result.status, "candidate")
        self.assertEqual(result.candidate, "plus-zero n")
        self.assertEqual(result.hints, ("plus-zero",))
        self.assertEqual(result.goal, unresolved.goal)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)
        handle, _ = session.give(initial, result.candidate)
        self.assertTrue(session.finalize(handle).task_success)

    def test_preserves_task_policy_and_honors_cancellation(self):
        project = copytree(self.fixture, self.root / "restricted")
        path = project / "completion.json"
        original = json.loads(path.read_bytes())
        original["allowed_edits"] = ["= (f (g x))"]
        path.write_text(json.dumps(original), encoding="utf-8")
        session = self.session(project=project)
        initial = session.handle

        with self.assertRaisesRegex(ValueError, "one millisecond"):
            session.auto(initial, timeout_s=0)
        with self.assertRaisesRegex(ValueError, "individual Agda names"):
            session.auto(initial, hints=("-t 500",))
        cancelled = Event()
        cancelled.set()
        with self.assertRaisesRegex(RuntimeError, "cancelled"):
            session.auto(initial, cancel=cancelled)
        result = session.auto(initial)
        self.assertEqual(result.candidate, "f (g x)")
        with self.assertRaisesRegex(ValueError, "allowed proof fragments"):
            session.give(initial, result.candidate)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)
        self.assertEqual(session.goal_context(initial), result.goal)

    def test_auto_checks_the_reviewed_multiline_rhs(self):
        project = copytree(self.fixture, self.root / "multiline")
        manifest = project / "completion.json"
        policy = json.loads(manifest.read_bytes())
        expected = "=\n  f (g x)"
        policy["allowed_edits"] = [expected, "= x"]
        manifest.write_text(json.dumps(policy), encoding="utf-8")
        session = self.session(project=project)
        driver = NativeProofDriver(session.task, session.prepared)

        suggestion = driver.suggest_atp()
        self.assertEqual(suggestion.outcome, "accepted")
        self.assertEqual(suggestion.action.text, "f (g x)")
        self.assertEqual(suggestion.candidate, expected)
        self.assertTrue(driver.apply_atp(suggestion).committed)
        checked = driver.finalize()
        self.assertEqual(checked.candidate, expected)
        self.assertTrue(checked.evidence.task_success)
