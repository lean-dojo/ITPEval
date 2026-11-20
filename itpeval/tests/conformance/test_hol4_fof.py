"""Exercise the trusted HOL4 exporter on native pending branches."""

import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from threading import Event

from itpeval.atp import prepare_solver
from itpeval.backends.hol4.fof import _sml_path, export_hol4_branch
from itpeval.backends.hol_tactics import HOLProofSession, HOLTraceFailure
from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/hol4/metis"


class HOL4PathTests(unittest.TestCase):
    def test_export_path_is_a_native_string_literal(self):
        self.assertEqual(_sml_path(Path('a"\\b')), '"\\097\\034\\092\\098"')


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native HOL4 checks")
class NativeHOL4ExportTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def _split(self, root: Path, *, output_limit: int | None = None):
        prepared = prepare_project("hol4", FIXTURE, prefix=self.prefix, cache=root / "cache")
        task = build_task(prepared)
        if output_limit is not None:
            task = replace(task, budgets=replace(task.budgets, max_log_bytes=output_limit))
        session = HOLProofSession(task, prepared)
        handle, _ = session.step(session.handle, (), "REPEAT DISCH_TAC")
        handle, state = session.step(handle, (0,), "CONJ_TAC")
        return session, handle, state

    def test_external_e_proves_both_exported_branches_before_independent_metis_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            session, handle, state = self._split(root)
            checkpoint = session.checkpoint(handle)
            solver = prepare_solver("e", prefix=self.prefix)
            problems = []
            for index, goal in enumerate(state.goals):
                problem = export_hol4_branch(session, goal.path, timeout_s=15)
                problems.append(problem)
                file = root / f"branch-{index}.p"
                file.write_text(problem, encoding="utf-8")
                found = solver.solve(file)
                self.assertEqual(found.native_status, "Theorem")
                self.assertTrue(found.certificate)
                self.assertEqual(session.checkpoint(handle), checkpoint)
                self.assertEqual(session.inspect(handle), state)
            self.assertNotEqual(*problems)

            handle, after_left = session.step(handle, (0, 0), "METIS_TAC []")
            self.assertEqual([goal.path for goal in after_left.goals], [(0, 1)])
            with self.assertRaisesRegex(ValueError, "current pending HOL4 goal path"):
                export_hol4_branch(session, (0, 0))
            handle, done = session.step(handle, (0, 1), "METIS_TAC []")
            self.assertFalse(done.goals)
            self.assertTrue(session.finalize(handle).task_success)

    def test_export_size_limit_and_cancellation_preserve_the_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            session, handle, state = self._split(Path(directory), output_limit=5000)
            checkpoint = session.checkpoint(handle)
            with self.assertRaisesRegex(ValueError, "output budget"):
                export_hol4_branch(session, (0, 0), timeout_s=15)
            cancel = Event()
            cancel.set()
            with self.assertRaisesRegex(HOLTraceFailure, "cancelled"):
                export_hol4_branch(session, (0, 1), cancel=cancel)
            self.assertEqual(session.checkpoint(handle), checkpoint)
            self.assertEqual(session.inspect(handle), state)
