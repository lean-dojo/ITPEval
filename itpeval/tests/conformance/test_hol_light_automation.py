"""Check scoped HOL Light first-order automation against the native kernel."""

from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase, skipUnless

from itpeval.backends.hol_light.worker import ForkedHOLLight
from itpeval.backends.hol_tactics import HOLProofCheckpoint, HOLProofSession, HOLTactic
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.verification.policies import assemble
from itpeval.verification.service import verify


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires the installed HOL Light prover")
class HOLLightAutomationTests(TestCase):
    def test_meson_uses_scoped_hypotheses_and_preserves_the_sibling_goal(self):
        project = curated_project("hol-light").parent / "automation"
        with TemporaryDirectory() as scratch:
            prepared = prepare_project("hol-light", project, cache=Path(scratch),
                                       prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
            task = build_task(prepared)
            intro = HOLTactic((), "DISCH_TAC", 1)
            split = HOLTactic((0,), "CONJ_TAC", 2)
            left = HOLTactic((0, 0), "ASM_MESON_TAC []", 0)
            right = HOLTactic((0, 1), "ASM_MESON_TAC []", 0)
            candidate = "((DISCH_TAC) THENL [((CONJ_TAC) THENL [ASM_MESON_TAC []; ASM_MESON_TAC []])])"

            def checkpoint(actions):
                return HOLProofCheckpoint(task.task_id, task.environment_id, actions)

            def cold_left():
                session = HOLProofSession.from_checkpoint(task, prepared, checkpoint((intro, split, left)))
                return session.inspect(session.handle)

            def warm_proof():
                with ForkedHOLLight(prepared) as worker:
                    session = HOLProofSession.from_checkpoint(task, prepared, checkpoint((intro, split)), worker=worker)
                    both = session.inspect(session.handle)
                    self.assertEqual([(goal.path, goal.conclusion) for goal in both.goals],
                                     [(left.path, "S a"), (right.path, "R a")])
                    self.assertTrue(all(any("R x ==> S x" in h and "R a" in h for h in goal.hypotheses)
                                        for goal in both.goals))
                    old = session.handle
                    handle, one = session.step(old, left.path, left.text)
                    self.assertNotEqual(handle, old)
                    self.assertEqual(one.goals, (both.goals[1],))
                    _, closed = session.step(handle, right.path, right.text)
                    self.assertEqual(closed.goals, ())
                    self.assertEqual(session.candidate, candidate)
                    return one

            with ThreadPoolExecutor(max_workers=3) as pool:
                cold = pool.submit(cold_left)
                strict = pool.submit(verify, task, candidate, prepared=prepared)
                warm = pool.submit(warm_proof) if ForkedHOLLight.supports_project(prepared) else None
                after_left = cold.result()
                self.assertEqual([(goal.path, goal.conclusion) for goal in after_left.goals], [(right.path, "R a")])
                self.assertIsNone(after_left.diagnostic)
                if warm is not None:
                    self.assertEqual(warm.result(), after_left)
                final = strict.result()
                self.assertIs(final.task_success, True, final.stdout[-2000:] + final.stderr[-2000:])
                self.assertEqual(final.artifact_id, assemble(task, candidate).artifact_id)
