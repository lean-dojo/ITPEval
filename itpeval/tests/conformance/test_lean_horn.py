"""Check the ground Horn fragment and optional native Lean replay."""

import json
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from itpeval.atp import LeanHornEvidence, LeanHornHypothesis, LeanHornProblem, observe_lean_horn, run_horn_search
from itpeval.backends.projects import build_task
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import LeanTacticSession


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/lean4/horn"
PREFIX_FIXTURE = FIXTURE.parent / "horn-prefix"
INTRODUCTIONS = ("intro hready hpermitted", "intro hdelivered hcomplete")


class LeanHornTests(unittest.TestCase):
    def test_ground_applications_are_distinct_and_tactic_syntax_is_rejected(self):
        first = LeanHornHypothesis("hq", ("p a",), "p b")
        problem = LeanHornProblem("p b", (first,))
        self.assertEqual(problem.to_tptp(), "fof(premise_0, axiom, ((p0) => p1)).\nfof(goal, conjecture, p1).\n")
        for text in ("∀ x, p x", "p (f a)", "by apply hp", "p _"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                LeanHornProblem(text, (first,))


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native Lean Horn checks")
class NativeLeanHornTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def test_external_search_uses_named_hypotheses_and_replays_a_lean_proof(self):
        problem = LeanHornProblem.from_dict(json.loads((FIXTURE / "horn.json").read_bytes()))
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            prepared = prepare_project("lean4", FIXTURE, prefix=self.prefix, cache=root / "cache")
            task = build_task(prepared)
            accepted = run_horn_search(task, problem, prepared=prepared)
            self.assertEqual(accepted.search.native_status, "Theorem")
            self.assertEqual(accepted.replay_outcome, "accepted")
            expected = ("hready", "hpermitted", "hdelivered", "hcomplete")
            self.assertEqual(accepted.certificate_hypotheses, expected)
            self.assertEqual(accepted.reconstructed_hypotheses, expected)
            self.assertEqual(dict(accepted.replay.obligations), {"completion_of_ready": "discharged"})
            self.assertIn("does not depend on any axioms", accepted.replay.stdout)
            self.assertEqual(LeanHornEvidence.from_dict(accepted.to_dict()), accepted)
            self.assertNotIn("suffix", accepted.to_dict())

            missing = replace(problem, hypotheses=problem.hypotheses[:3])
            counterexample = run_horn_search(task, missing, prepared=prepared)
            self.assertEqual(counterexample.search.native_status, "CounterSatisfiable")
            self.assertIsNone(counterexample.replay)

            # The ATP sees the same abstract Horn inference. Lean must reject
            # this mapping because `_hextra` proves a different proposition.
            wrong_hypothesis = replace(problem.hypotheses[0], name="_hextra")
            mismapped = replace(problem, hypotheses=(wrong_hypothesis, *problem.hypotheses[1:4]))
            blocked = run_horn_search(task, mismapped, prepared=prepared)
            self.assertEqual(blocked.search.native_status, "Theorem")
            self.assertEqual(blocked.replay_outcome, "outside_task_policy")
            self.assertIsNone(blocked.replay)

            project = root / "mismapped"
            project.mkdir()
            (project / "Delivery.lean").write_bytes((FIXTURE / "Delivery.lean").read_bytes())
            manifest = json.loads((FIXTURE / "completion.json").read_bytes())
            manifest["allowed_edits"] = [blocked.candidate]
            (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            locked = prepare_project("lean4", project, prefix=self.prefix, cache=root / "cache")
            rejected = run_horn_search(build_task(locked), mismapped, prepared=locked)
            self.assertEqual(rejected.search.native_status, "Theorem")
            self.assertEqual(rejected.replay_outcome, "rejected")
            self.assertFalse(rejected.replay.task_success)
            self.assertIn("Type mismatch", rejected.replay.stdout)

    def test_discovers_clauses_from_an_unfinished_locked_proof_without_a_map(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "project"
            project.mkdir()
            manifest = json.loads((FIXTURE / "completion.json").read_bytes())
            starter = manifest["proof_slot"]
            invalid_proof = "exact False.elim"
            extra = "(_hextra : extra item)"
            compound = extra + " (_hcompound : ready item ∧ extra item)"
            source = (FIXTURE / "Delivery.lean").read_text(encoding="utf-8")
            source = "import Std\n\n" + source.replace(extra, compound).replace(starter, invalid_proof)
            (project / "Delivery.lean").write_text(source, encoding="utf-8")
            manifest["proof_slot"] = invalid_proof
            manifest["anchor"] = manifest["anchor"].replace(extra, compound).replace(starter, invalid_proof)
            manifest["statement"] = manifest["statement"].replace("extra item → complete item", (
                "extra item → (ready item ∧ extra item) → complete item"))
            (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            prepared = prepare_project("lean4", project, prefix=self.prefix, cache=root / "cache")
            task = build_task(prepared)

            receipt = run_horn_search(task, prepared=prepared)
            observation = receipt.observation
            self.assertEqual(observation.goal, "complete item")
            self.assertEqual(observation.slot_byte_offset, source.encode().index(invalid_proof.encode()))
            self.assertEqual(observation.skipped_propositions, ("_hcompound",))
            self.assertEqual(observation.problem, receipt.problem)
            names = tuple(hypothesis.name for hypothesis in observation.problem.hypotheses)
            self.assertEqual(names, ("hready", "hpermitted", "hdelivered", "hcomplete", "_hextra"))
            self.assertNotIn("_hextra", receipt.certificate_hypotheses)
            self.assertEqual(receipt.replay_outcome, "accepted")
            self.assertEqual(LeanHornEvidence.from_dict(receipt.to_dict()), receipt)

    def test_native_equality_goal_is_outside_the_automatic_ground_fragment(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared = prepare_project("lean4", FIXTURE.parent / "completion",
                                       prefix=self.prefix, cache=Path(temp))
            task = build_task(prepared)
            observation = observe_lean_horn(task, prepared=prepared)
            self.assertEqual(observation.goal, "x = x")
            self.assertIsNone(observation.problem)
            with self.assertRaisesRegex(ValueError, "no supported local Horn problem"):
                run_horn_search(task, prepared=prepared)

    def test_discovers_and_applies_a_single_horn_suffix_after_the_committed_prefix(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared = prepare_project("lean4", PREFIX_FIXTURE, prefix=self.prefix, cache=Path(temp))
            task = build_task(prepared)
            initial = observe_lean_horn(task, prepared=prepared)
            self.assertIsNone(initial.problem)
            self.assertNotIn("prefix", initial.to_dict())
            self.assertNotIn("probe_byte_offset", initial.to_dict())
            session = LeanTacticSession(task, prepared)
            for tactic in INTRODUCTIONS:
                _, progressed = session.step(session.handle, tactic)
            self.assertIn("⊢ complete item", progressed["after"]["goal"]["goals"][0])

            receipt = run_horn_search(task, prepared=prepared, prefix=INTRODUCTIONS, as_action=True)
            self.assertEqual(receipt.observation.prefix, INTRODUCTIONS)
            self.assertEqual(receipt.observation.artifact_id, task.artifact.artifact_id)
            prefix_source = " <;> ".join(INTRODUCTIONS) + "\n  "
            self.assertEqual(receipt.observation.probe_byte_offset, task.editable_regions[0].start
                             + len(prefix_source.encode("utf-8")))
            self.assertEqual(receipt.problem.conclusion, "complete item")
            names = tuple(hypothesis.name for hypothesis in receipt.problem.hypotheses)
            self.assertEqual(names, ("hready", "hpermitted", "hdelivered", "hcomplete"))
            self.assertEqual(receipt.search.native_status, "Theorem")
            self.assertEqual(receipt.certificate_hypotheses, names)
            self.assertEqual(receipt.replay_outcome, "accepted")
            self.assertEqual(receipt.candidate, " <;> ".join((*INTRODUCTIONS, receipt.suffix)))
            self.assertEqual(LeanHornEvidence.from_dict(receipt.to_dict()), receipt)
            handle, finished = session.step(session.handle, receipt.suffix)
            self.assertFalse(finished["after"]["goal"]["goals"])
            self.assertEqual(session.candidate, receipt.candidate)
            self.assertEqual(session.finalize(handle).artifact_id, receipt.replay.artifact_id)
            self.assertIn("does not depend on any axioms", receipt.replay.stdout)
            with self.assertRaisesRegex(ValueError, "one open Lean goal|no goals to be solved"):
                observe_lean_horn(task, prepared=prepared, prefix=(*INTRODUCTIONS, receipt.suffix))

    def test_rejects_a_failed_or_multigoal_prefix_before_search(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "project"
            project.mkdir()
            proof = "exact ⟨hp, hp⟩"
            declaration = f"theorem split_goal (p : Prop) (hp : p) : p ∧ p := by\n  {proof}"
            (project / "Split.lean").write_text(declaration + "\n", encoding="utf-8")
            manifest = {"schema_version": 1, "entrypoint": "Split.lean", "files": ["Split.lean"],
                        "anchor": declaration, "target": "split_goal", "statement": "∀ (p : Prop), p → p ∧ p",
                        "proof_slot": proof, "allowed_edits": [proof], "proof_atoms": ["constructor", "exact False.elim"]}
            (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            prepared = prepare_project("lean4", project, prefix=self.prefix, cache=root / "cache")
            task = build_task(prepared)
            with self.assertRaisesRegex(ValueError, "Type mismatch"):
                observe_lean_horn(task, prepared=prepared, prefix=("exact False.elim",))
            with self.assertRaisesRegex(ValueError, "one open Lean goal"):
                run_horn_search(task, prepared=prepared, prefix=("constructor",))
            with self.assertRaisesRegex(ValueError, "allowed proof fragments"):
                observe_lean_horn(task, prepared=prepared, prefix=("rfl",))

    def test_supported_native_goal_without_hypotheses_has_a_countermodel(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "empty_context"
            project.mkdir()
            declaration = "theorem empty_context : ground_goal := by\n  exact True.intro"
            source = "def ground_goal : Prop := True\n\n" + declaration + "\n"
            (project / "EmptyContext.lean").write_text(source, encoding="utf-8")
            manifest = {"schema_version": 1, "entrypoint": "EmptyContext.lean", "files": ["EmptyContext.lean"],
                        "anchor": declaration, "target": "empty_context", "statement": "ground_goal",
                        "proof_slot": "exact True.intro", "allowed_edits": ["exact True.intro"]}
            (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            prepared = prepare_project("lean4", project, prefix=self.prefix, cache=root / "cache")
            result = run_horn_search(build_task(prepared), prepared=prepared)
            self.assertEqual(result.observation.goal, "ground_goal")
            self.assertEqual(result.problem.hypotheses, ())
            self.assertEqual(result.search.native_status, "CounterSatisfiable")
            self.assertEqual(result.replay_outcome, "not_attempted")
            self.assertIsNone(result.replay)
