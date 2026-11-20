"""Check that Rocq confirms the exact goal and rejects wrong premise mappings."""

import json
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from itpeval.atp import RocqHornEvidence, RocqHornProblem, observe_rocq_horn, run_rocq_horn_search
from itpeval.backends.projects import build_task
from itpeval.backends.rocq.interaction import RocqIDESession
from itpeval.environments import prepare_project
from itpeval.learning.assisted import episode_from_search


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures/projects/rocq/horn"


@unittest.skipUnless(os.getenv("ITPEVAL_REAL_ATP_PREFIX"), "set ITPEVAL_REAL_ATP_PREFIX for native Rocq Horn checks")
class NativeRocqHornTests(unittest.TestCase):
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def _locked_task(self, root, name, declaration, statement, slot, *, allowed=None):
        project = root / name
        project.mkdir()
        (project / "Context.v").write_text(declaration + "\n", encoding="utf-8")
        manifest = {"schema_version": 1, "entrypoint": "Context.v", "files": ["Context.v"],
                    "anchor": declaration, "target": name, "statement": statement,
                    "proof_slot": slot, "allowed_edits": [slot] if allowed is None else allowed}
        (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
        prepared = prepare_project("rocq", project, prefix=self.prefix, cache=root / "cache")
        return prepared, build_task(prepared)

    def test_rocq_replay_and_separation_from_search_only_outcomes(self):
        problem = RocqHornProblem.from_dict(json.loads((FIXTURE / "horn.json").read_bytes()))
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            prepared = prepare_project("rocq", FIXTURE, prefix=self.prefix, cache=root / "cache")
            task = build_task(prepared)
            result = run_rocq_horn_search(task, problem, prepared=prepared)
            expected = ("hready", "hpermitted", "hdelivered", "hcomplete")
            self.assertEqual(result.search.native_status, "Theorem")
            self.assertEqual(result.certificate_hypotheses, expected)
            self.assertEqual(result.reconstructed_hypotheses, expected)
            self.assertEqual(result.replay_outcome, "accepted")
            self.assertEqual(dict(result.replay.obligations), {"completion_of_ready": "discharged"})
            self.assertIn("Closed under the global context", result.replay.stdout)
            self.assertEqual(RocqHornEvidence.from_dict(result.to_dict()), result)
            episode = episode_from_search(task, result)
            self.assertTrue(episode.transitions[0].observation.task_success)

            missing = replace(problem, hypotheses=problem.hypotheses[:3])
            counterexample = run_rocq_horn_search(task, missing, prepared=prepared)
            self.assertEqual(counterexample.search.native_status, "CounterSatisfiable")
            self.assertIsNone(episode_from_search(task, counterexample))

            # `_hextra` inhabits `extra item`. Changing its abstract label to
            # `ready item` leaves the solver's theorem intact but fails in Rocq.
            mapped = replace(problem.hypotheses[0], name="_hextra")
            mismatch = replace(problem, hypotheses=(mapped, *problem.hypotheses[1:4]))
            blocked = run_rocq_horn_search(task, mismatch, prepared=prepared)
            self.assertEqual(blocked.search.native_status, "Theorem")
            self.assertEqual(blocked.replay_outcome, "outside_task_policy")
            self.assertIsNone(episode_from_search(task, blocked))

            project = root / "mismatch"
            project.mkdir()
            (project / "Delivery.v").write_bytes((FIXTURE / "Delivery.v").read_bytes())
            manifest = json.loads((FIXTURE / "completion.json").read_bytes())
            manifest["allowed_edits"] = [blocked.candidate]
            (project / "completion.json").write_text(json.dumps(manifest), encoding="utf-8")
            locked = prepare_project("rocq", project, prefix=self.prefix, cache=root / "cache")
            mismatched_task = build_task(locked)
            rejected = run_rocq_horn_search(mismatched_task, mismatch, prepared=locked)
            self.assertEqual(rejected.search.native_status, "Theorem")
            self.assertEqual(rejected.replay_outcome, "rejected")
            self.assertFalse(rejected.replay.task_success)
            self.assertIn("expected to have type", rejected.replay.stderr)
            episode = episode_from_search(mismatched_task, rejected)
            self.assertFalse(episode.transitions[0].observation.task_success)

    def test_native_discovery_from_a_locked_source_without_a_map(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = json.loads((FIXTURE / "completion.json").read_bytes())
            extra = "(_hextra : extra item)"
            excluded = (extra + " (_hcompound : ready item /\\ extra item)\n"
                        "    (_hquantified : forall x : Item, ready x -> complete x)")
            starter = manifest["proof_slot"]
            invalid = "exact I."
            declaration = manifest["anchor"].replace(extra, excluded).replace(
                starter, "(* Read the goal before replacing this proof. *)\n  " + invalid)
            statement = manifest["statement"].replace("extra item -> complete item", (
                "extra item -> (ready item /\\ extra item) -> "
                "(forall x : Item, ready x -> complete x) -> complete item"))
            prepared, task = self._locked_task(root, manifest["target"], declaration, statement, invalid,
                                               allowed=manifest["allowed_edits"])
            receipt = run_rocq_horn_search(task, prepared=prepared)
            state = receipt.observation
            self.assertEqual(state.goal, "complete item")
            self.assertEqual(state.slot_byte_offset, declaration.encode().index(invalid.encode()))
            self.assertEqual(state.problem, receipt.problem)
            self.assertEqual(state.skipped_propositions, ("_hcompound", "_hquantified"))
            self.assertEqual(tuple(hypothesis.name for hypothesis in state.problem.hypotheses),
                             ("hready", "hpermitted", "hdelivered", "hcomplete", "_hextra"))
            self.assertNotIn("_hextra", receipt.certificate_hypotheses)
            self.assertEqual(receipt.replay_outcome, "accepted")
            self.assertIn("Closed under the global context", receipt.replay.stdout)
            self.assertEqual(RocqHornEvidence.from_dict(receipt.to_dict()), receipt)
            episode = episode_from_search(task, receipt)
            self.assertEqual(episode.manifest["model_config"]["premise_source"], "native_tactic_state")

    def test_automatic_rocq_observes_unsupported_goals_without_search(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            equal = "Theorem equality_goal (n : nat) : n = n.\nProof.\n  reflexivity.\nQed."
            prepared, task = self._locked_task(root, "equality_goal", equal, "forall n : nat, n = n", "reflexivity.")
            state = observe_rocq_horn(task, prepared=prepared)
            self.assertEqual(state.focused_goals, 1)
            self.assertEqual(state.goal, "n = n")
            self.assertEqual(state.reason, "outside_ground_fragment")
            self.assertIsNone(state.problem)

            split = "Theorem split_goal (p : Prop) (hp : p) : p /\\ p.\nProof.\n  split.\n  all: exact hp.\nQed."
            prepared, task = self._locked_task(root, "split_goal", split, "forall p : Prop, p -> p /\\ p",
                                               "all: exact hp.")
            state = observe_rocq_horn(task, prepared=prepared)
            self.assertEqual(state.focused_goals, 2)
            self.assertEqual(state.reason, "multiple_or_unfocused_goals")
            self.assertIsNone(state.problem)

    def test_automatic_rocq_retains_global_axiom_policy(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared = prepare_project("rocq", FIXTURE.parent / "horn-policy", prefix=self.prefix, cache=Path(temp))
            result = run_rocq_horn_search(build_task(prepared, "global-completion.json"), prepared=prepared)
            self.assertEqual(result.observation.goal, "p")
            self.assertEqual(result.problem.hypotheses, ())
            self.assertEqual(result.search.native_status, "CounterSatisfiable")
            self.assertIsNone(result.replay)

            result = run_rocq_horn_search(build_task(prepared, "local-completion.json"), prepared=prepared)
            self.assertEqual(result.search.native_status, "Theorem")
            self.assertEqual(result.certificate_hypotheses, ("hOracle",))
            self.assertEqual(result.replay_outcome, "rejected")
            self.assertEqual(result.replay.checker_outcome, "policy_rejected")
            self.assertIn("Unauthorized dependencies: oracle", result.replay.stderr)

    def test_recovers_a_single_native_action_after_intro_and_replays_the_full_proof(self):
        with tempfile.TemporaryDirectory() as temp:
            prepared = prepare_project("rocq", FIXTURE.parent / "horn-prefix", prefix=self.prefix, cache=Path(temp))
            task = build_task(prepared)
            initial = observe_rocq_horn(task, prepared=prepared)
            self.assertEqual(initial.goal, "p -> q")
            self.assertIsNone(initial.problem)

            prefix = ("intro hp.",)
            result = run_rocq_horn_search(task, prepared=prepared, prefix=prefix)
            self.assertEqual(result.observation.goal, "q")
            self.assertEqual(result.observation.prefix, prefix)
            self.assertEqual(result.reconstructed_hypotheses, ("hp", "hpq"))
            self.assertEqual(result.candidate, "\n".join((*prefix, result.suffix)))
            self.assertEqual(result.replay_outcome, "accepted")
            self.assertEqual(dict(result.replay.obligations), {"follows_after_intro": "discharged"})
            self.assertIn("Closed under the global context", result.replay.stdout)
            self.assertEqual(RocqHornEvidence.from_dict(result.to_dict()), result)

            session = RocqIDESession(task, prepared)
            handle, _ = session.step(session.handle, prefix[0])
            handle, state = session.step(handle, result.suffix)
            self.assertTrue(state.complete)
            self.assertEqual(session.candidate, result.candidate)
            self.assertTrue(session.finalize(handle).task_success)

            restricted = build_task(prepared, "restricted-completion.json")
            blocked = run_rocq_horn_search(restricted, prepared=prepared, prefix=prefix)
            self.assertEqual(blocked.search.native_status, "Theorem")
            self.assertEqual(blocked.suffix, result.suffix)
            self.assertEqual(blocked.replay_outcome, "outside_task_policy")
            self.assertIsNone(blocked.replay)
            with self.assertRaisesRegex(ValueError, "prefix command 1 is outside the task policy"):
                observe_rocq_horn(task, prepared=prepared, prefix=("intro different.",))

            closed = observe_rocq_horn(task, prepared=prepared, prefix=(*prefix, "exact (hpq hp)."))
            self.assertEqual(closed.reason, "no_open_goal")
            self.assertIsNone(closed.problem)

    def test_initial_state_can_request_a_single_action(self):
        with tempfile.TemporaryDirectory() as temp:
            declaration = "Theorem direct (p : Prop) (hp : p) : p.\nProof.\n  exact hp.\nQed."
            suffix = "exact (let hornFact0 : (p : Prop) := hp in\n    hornFact0)."
            prepared, task = self._locked_task(Path(temp), "direct", declaration, "forall p : Prop, p -> p",
                                               "exact hp.", allowed=[suffix])
            result = run_rocq_horn_search(task, prepared=prepared, as_action=True)
            self.assertEqual(result.candidate, suffix)
            self.assertEqual(result.suffix, suffix)
            self.assertEqual(result.replay_outcome, "accepted")

    def test_prefix_replay_still_checks_unauthorized_assumptions(self):
        with tempfile.TemporaryDirectory() as temp:
            declaration = ("Axiom oracle : forall p : Prop, p.\n\n"
                           "Theorem axiom_prefix (p : Prop) : p.\nProof.\n  exact (oracle p).\nQed.")
            command = "assert (hOracle : p) by exact (oracle p)."
            suffix = "exact (let hornFact0 : (p : Prop) := hOracle in\n    hornFact0)."
            prepared, task = self._locked_task(Path(temp), "axiom_prefix", declaration, "forall p : Prop, p",
                                               "exact (oracle p).", allowed=[command, command + "\n" + suffix])
            result = run_rocq_horn_search(task, prepared=prepared, prefix=(command,))
            self.assertEqual(result.search.native_status, "Theorem")
            self.assertEqual(result.suffix, suffix)
            self.assertEqual(result.replay_outcome, "rejected")
            self.assertEqual(result.replay.checker_outcome, "policy_rejected")
            self.assertIn("Unauthorized dependencies: oracle", result.replay.stderr)
