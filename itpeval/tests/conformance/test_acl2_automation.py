"""Exercise scope, review, and strict final checks for native ACL2 automation."""

import json
import os
from pathlib import Path
from shutil import copytree
from tempfile import TemporaryDirectory
from unittest import TestCase, skipUnless

from itpeval.backends.acl2.interaction import ACL2ProofBuilderSession, ACL2TraceFailure
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.verification.service import verify


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed ACL2")
class ACL2AutomationTests(TestCase):
    def setUp(self):
        scratch = TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        self.fixture = curated_project("acl2").parent / "automation"

    def prepare(self, project):
        prepared = prepare_project("acl2", project, cache=self.root / "cache",
                                   prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
        return prepared, build_task(prepared)

    def test_scoped_automation_progress_rejection_timeout_and_strict_proof(self):
        prepared, task = self.prepare(self.fixture)
        session = ACL2ProofBuilderSession(task, prepared)
        original = session.inspect(session.handle)
        self.assertIn("no top-level hypotheses", original.hypotheses)
        handle, scoped = session.step(session.handle, "promote")
        self.assertIn("(EQUAL (CAR XS) A)", scoped.hypotheses)
        self.assertIn("(EQUAL (CONS A TAIL) YS)", scoped.hypotheses)
        self.assertEqual(session.automation_commands(handle), ("s", "bash"))

        branch = session.fork(handle)
        self.assertIs(branch.inspect(branch.handle), scoped)
        old = branch.handle
        with self.assertRaises(ACL2TraceFailure) as expired:
            branch.step(old, "s", timeout_s=0.000001)
        self.assertEqual(expired.exception.outcome, "timeout")
        self.assertEqual(branch.handle, old)

        simplified, remaining = branch.step(old, "s")
        self.assertNotEqual(simplified, old)
        self.assertFalse(remaining.complete)
        self.assertEqual(remaining.focused_term, "(EQUAL A (CAR YS))")
        unchanged, no_progress = branch.step(simplified, "s")
        self.assertEqual(unchanged, simplified)
        self.assertIn("No simplification took place", no_progress.diagnostic)
        self.assertIs(branch.inspect(unchanged), remaining)

        closed, solved = branch.step(unchanged, "bash")
        self.assertTrue(solved.complete)
        self.assertEqual(branch.candidate, ":instructions (:promote :s :bash)")
        self.assertEqual(branch.automation_commands(closed), ())
        self.assertIs(branch.finalize(closed).task_success, True)
        self.assertIs(verify(task, ":instructions (:promote :s)", prepared=prepared).task_success, False)
        self.assertIs(session.inspect(handle), scoped)

    def test_automatic_candidates_cannot_exceed_the_reviewed_prefix_policy(self):
        project = self.root / "restricted"
        copytree(self.fixture, project)
        manifest = project / "completion.json"
        review = json.loads(manifest.read_text())
        review.update(allowed_edits=[":instructions (:promote :s)"], proof_atoms=[":promote", ":s"])
        manifest.write_text(json.dumps(review), encoding="utf-8")
        prepared, task = self.prepare(project)
        branch = ACL2ProofBuilderSession(task, prepared)
        handle, _ = branch.step(branch.handle, "promote")
        self.assertEqual(branch.automation_commands(handle), ("s",))
        finished, solved = branch.step(handle, "bash")
        self.assertTrue(solved.complete)
        final = branch.finalize(finished)
        self.assertEqual((final.execution_outcome, final.checker_outcome, final.task_success),
                         ("not_run", "policy_rejected", False))
