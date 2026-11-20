"""Exercise the ATP evidence contract and optional native integrations."""
import os
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from itpeval.atp import SOLVERS, SearchEvidence, run_sledgehammer, solve_tptp
from itpeval.atp.isabelle import PremisePool, _search_messages
from itpeval.atp.search import _parse_search
from itpeval.atp.tptp import stage_problem
from itpeval.backends.projects import build_task
from itpeval.core.types import Budgets
from itpeval.environments import prepare_project
from itpeval.runtime.process import ProcessResult


FIXTURES = Path(__file__).resolve().parents[1] / "fixtures/projects"


class TPTPStagingTests(unittest.TestCase):
    def test_snapshots_nested_includes_without_rewriting_formulas(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            axioms = root / "Axioms"
            axioms.mkdir()
            (axioms / "base.ax").write_text("fof(fact,axiom,p(a)).\n")
            (axioms / "main.ax").write_text("include('base.ax',[fact]).\n")
            source = root / "case.p"
            source.write_text("% include('fake.ax').\n"
                              "include('Axioms/main.ax').\n"
                              "fof(claim,conjecture,p(a)).\n")
            workspace = root / "stage"
            workspace.mkdir()
            entry, staged, files = stage_problem(source, root, workspace)
            self.assertEqual(entry, "case.p")
            receipt = {name: (native, original_hash, staged_hash)
                       for name, original_hash, native, staged_hash in files}
            self.assertEqual(set(receipt), {"case.p", "Axioms/main.ax", "Axioms/base.ax"})
            self.assertEqual(receipt["Axioms/base.ax"][1], receipt["Axioms/base.ax"][2])
            self.assertIn("% include('fake.ax').", (workspace / staged).read_text())
            self.assertIn("fof(claim,conjecture,p(a)).", (workspace / staged).read_text())
            main = (workspace / receipt["Axioms/main.ax"][0]).read_text()
            self.assertEqual(main, f"include('{receipt['Axioms/base.ax'][0]}',[fact]).\n")

    def test_include_cycles_and_outside_sources_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "case.p").write_text("include('cycle.ax').\n")
            (root / "cycle.ax").write_text("include('case.p').\n")
            with self.assertRaisesRegex(ValueError, "cyclic"):
                stage_problem(root / "case.p", root, root)
            (root / "case.p").write_text("include('../unsafe.ax').\n")
            with self.assertRaises(ValueError):
                stage_problem(root / "case.p", root, root)


class ATPEvidenceTests(unittest.TestCase):
    def test_process_outcomes_take_precedence_over_printed_success(self):
        report = "% SZS status Theorem for sample"
        for process, expected in [
            (ProcessResult(-1, "cancelled", report, "", 25, False), "cancelled"),
            (ProcessResult(0, "exited", report, "", 25, True), "output_truncated"),
            (ProcessResult(0, "exited", report + "\n% SZS status GaveUp", "", 25, False), "protocol_error"),
            (ProcessResult(1, "exited", "% SZS status GaveUp", "", 25, False), "unknown"),
        ]:
            with self.subTest(expected=expected):
                self.assertEqual(_parse_search("e", process)[1], expected)

    def test_only_suggestions_at_the_target_command_are_collected(self):
        path = Path("/tmp/Hammer.thy")
        log = f"""
Output (line 5 of "{path}"):
e: Try this: by (metis unrelated)

Output (line 9 of "{path}"):
e: Try this: by (metis assumption)
  (0.8 ms)

Output (line 9 of "{path}"):
e found a proof...

Output (line 9 of "{path}"):
Selected 2 mepo facts: premise lemma
Selected 1 mesh fact: hypothesis
"""
        self.assertEqual(_search_messages(log, path, 9, "e"), (
            True, ["by (metis assumption)"],
            (PremisePool("mepo", 2, ("premise", "lemma")), PremisePool("mesh", 1, ("hypothesis",))),
        ))


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native ATP checks")
class NativeATPTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def test_standalone_e_and_vampire(self):
        for solver in SOLVERS:
            with self.subTest(solver=solver):
                theorem = solve_tptp(FIXTURES / "tptp/socrates.p", solver=solver, prefix=self.prefix)
                self.assertEqual(theorem.native_status, "Theorem")
                self.assertTrue(theorem.certificate)
                self.assertEqual(SearchEvidence.from_dict(theorem.to_dict()), theorem)
                counter = solve_tptp(FIXTURES / "tptp/counterexample.p", solver=solver, prefix=self.prefix)
                self.assertEqual(counter.native_status, "CounterSatisfiable")
                contradiction = solve_tptp(FIXTURES / "tptp/contradictory.p", solver=solver, prefix=self.prefix)
                self.assertEqual(contradiction.outcome, "contradictory_axioms")
                timed = solve_tptp(FIXTURES / "tptp/socrates.p", solver=solver, prefix=self.prefix,
                                    budgets=Budgets(timeout_s=.005))
                self.assertEqual(timed.outcome, "timeout")

    def test_hammer_replay_and_policy_separation(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared = prepare_project("isabelle", FIXTURES / "isabelle/hammer", prefix=self.prefix, cache=Path(temp))
            task = build_task(prepared)
            for solver in SOLVERS:
                with self.subTest(solver=solver):
                    result = run_sledgehammer(task, prepared=prepared, solver=solver, search_timeout_s=30,
                                              replay_limit=1)
                    self.assertEqual(result.search_outcome, "proof_found")
                    self.assertIsNotNone(result.checked_proof)
                    self.assertTrue(result.premise_pools)
                    self.assertEqual(dict(result.checked_proof.evidence.obligations),
                                     {"reverse_append_probe": "discharged"})
            restricted = build_task(prepared, "restricted-completion.json")
            blocked = run_sledgehammer(restricted, prepared=prepared, search_timeout_s=30)
            self.assertEqual(blocked.search_outcome, "proof_found")
            self.assertIsNone(blocked.checked_proof)
            self.assertTrue(all(proof.disposition == "outside_task_policy" for proof in blocked.suggestions))

    def test_hammer_replays_a_suggestion_when_the_starter_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "project"
            project.mkdir()
            fixture = FIXTURES / "isabelle/hammer"
            (project / "ROOT").write_bytes((fixture / "ROOT").read_bytes())
            starter = "by (rule FalseE)"
            source = (fixture / "HammerDemo.thy").read_text().replace("by simp", starter)
            (project / "HammerDemo.thy").write_text(source)
            manifest = json.loads((fixture / "completion.json").read_bytes())
            manifest["anchor"] = manifest["anchor"].replace("by simp", starter)
            manifest["proof_slot"] = starter
            (project / "completion.json").write_text(json.dumps(manifest))
            prepared = prepare_project("isabelle", project, prefix=self.prefix, cache=root / "cache")
            def include_second_candidate(*args):
                found, candidates, pools = _search_messages(*args)
                if candidates:
                    candidates.append("by auto")
                return found, candidates, pools

            with patch("itpeval.atp.isabelle._search_messages", side_effect=include_second_candidate):
                result = run_sledgehammer(build_task(prepared), prepared=prepared,
                                          search_timeout_s=30, replay_limit=2)
            self.assertNotEqual(result.search.returncode, 0)
            self.assertIsNotNone(result.checked_proof, (result.search_outcome, result.suggestions,
                                                        result.search.stdout[-2000:], result.search.stderr[-1500:]))
            self.assertEqual(result.checked_proof.evidence.checker_outcome, "accepted")
            self.assertEqual(result.suggestions[-1].disposition, "replay_already_finished")
            self.assertIsNone(result.suggestions[-1].evidence)


if __name__ == "__main__":
    unittest.main()
