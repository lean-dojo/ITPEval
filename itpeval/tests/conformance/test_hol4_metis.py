"""Check reviewed Metis on individual pending goals in an installed HOL4."""

import os
import tempfile
import unittest
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/hol4/metis"


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native HOL4 checks")
class NativeHOL4MetisTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def test_metis_uses_local_premises_on_each_pending_branch(self):
        with tempfile.TemporaryDirectory() as directory:
            prepared = prepare_project("hol4", FIXTURE, prefix=self.prefix, cache=Path(directory))
            driver = NativeProofDriver(build_task(prepared), prepared)

            introduced = driver.advance(NativeProofAction("tactic", "REPEAT DISCH_TAC", ()))
            self.assertTrue(introduced.committed)
            split = driver.advance(NativeProofAction("tactic", "CONJ_TAC", (0,)))
            self.assertTrue(split.committed)
            goals = split.observation.native["goals"]
            self.assertEqual([(goal["path"], goal["conclusion"]) for goal in goals],
                             [([0, 0], "q n"), ([0, 1], "r n")])
            for goal in goals:
                self.assertEqual(set(goal["hypotheses"]), {"p n", "∀x. p x ⇒ q x", "∀x. q x ⇒ r x"})

            rejected = driver.advance(NativeProofAction("tactic", "NO_TAC", (0, 0)))
            self.assertFalse(rejected.committed)
            self.assertEqual(driver.observe(), split.observation)

            branch = driver.fork()
            left = branch.advance(NativeProofAction("tactic", "METIS_TAC []", (0, 0)))
            self.assertTrue(left.committed)
            self.assertEqual(left.observation.status, "open")
            self.assertEqual([goal["path"] for goal in left.observation.native["goals"]], [[0, 1]])
            self.assertEqual(driver.observe(), split.observation)

            right = branch.advance(NativeProofAction("tactic", "METIS_TAC []", (0, 1)))
            self.assertTrue(right.committed)
            self.assertEqual(right.observation.status, "ready")
            checked = branch.finalize()
            self.assertTrue(checked.evidence.task_success)
            self.assertEqual(dict(checked.evidence.obligations), {"follows_from_local_rules": "discharged"})
