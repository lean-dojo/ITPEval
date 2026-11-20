"""Exercise Agda ground Horn discovery, solver attribution and native replay."""

import json
import os
from pathlib import Path
from shutil import copytree
from tempfile import TemporaryDirectory
from unittest import TestCase, skipUnless

from itpeval.atp.agda import AgdaHornEvidence, AgdaHornHypothesis, observe_agda_horn, run_agda_horn_search
from itpeval.atp.search import prepare_solver
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import AgdaHoleSession, agda_term_candidate
from itpeval.verification.policies import assemble


@skipUnless(os.environ.get("ITPEVAL_REAL_ATP_PREFIX"), "requires installed Agda and E")
class NativeAgdaHornTests(TestCase):
    fixture = curated_project("agda").parent / "horn"
    prefix = Path(os.environ.get("ITPEVAL_REAL_ATP_PREFIX", "."))

    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def prepare(self, project=None, manifest="completion.json"):
        prepared = prepare_project("agda", project or self.fixture, cache=self.root / "cache", prefix=self.prefix)
        return build_task(prepared, manifest), prepared

    def check_replay_and_policy(self, solver):
        task, prepared = self.prepare()
        session = AgdaHoleSession(task, prepared)
        initial = session.handle
        receipt = run_agda_horn_search(task, prepared=prepared, solver=solver)
        context = session.goal_context(initial)
        self.assertEqual(receipt.observation.context, context)
        self.assertEqual(receipt.observation.artifact_id, task.artifact.artifact_id)
        self.assertEqual(receipt.observation.slot_byte_offset, task.editable_regions[0].start)
        self.assertEqual(receipt.problem.conclusion, "Complete item")
        self.assertIn(AgdaHornHypothesis("transit", ("Ready item", "Permitted item"), "Delivered item"),
                      receipt.problem.hypotheses)
        self.assertEqual(receipt.search.native_status, "Theorem")
        named = ("ready", "permitted", "transit", "finish")
        self.assertEqual(receipt.certificate_hypotheses, named)
        self.assertEqual(receipt.reconstructed_hypotheses, named)
        self.assertEqual(receipt.replay_outcome, "accepted")
        self.assertEqual(receipt.candidate, task.allowed_edits[0])
        self.assertEqual(agda_term_candidate(task, receipt.suffix), receipt.candidate)
        self.assertEqual(receipt.replay.artifact_id, assemble(task, receipt.candidate).artifact_id)
        self.assertEqual(AgdaHornEvidence.from_dict(receipt.to_dict()), receipt)

        fork = session.fork(initial)
        handle, _ = fork.give(fork.handle, receipt.suffix)
        self.assertEqual(handle.revision, 1)
        self.assertEqual(session.handle, initial)
        self.assertIsNone(session.candidate)
        checked = fork.finalize(handle)
        self.assertTrue(checked.task_success)
        self.assertEqual(checked.artifact_id, receipt.replay.artifact_id)
        with self.assertRaisesRegex(ValueError, "stale or foreign"):
            session.give(handle, receipt.suffix)
        handle, _ = session.give(initial, receipt.suffix)
        self.assertEqual(session.candidate, receipt.candidate)
        self.assertEqual(session.finalize(handle).obligations, (("deliver", "discharged"),))

        project = copytree(self.fixture, self.root / "restricted")
        manifest = project / "completion.json"
        policy = json.loads(manifest.read_bytes())
        policy["allowed_edits"] = ["= finish (transit ready permitted)"]
        manifest.write_text(json.dumps(policy), encoding="utf-8")
        restricted, locked = self.prepare(project)
        outside = run_agda_horn_search(restricted, prepared=locked, solver=solver)
        self.assertEqual(outside.search.native_status, "Theorem")
        self.assertEqual(outside.replay_outcome, "outside_task_policy")
        self.assertIsNone(outside.replay)
        rejected = AgdaHoleSession(restricted, locked)
        unchanged = rejected.handle
        with self.assertRaisesRegex(ValueError, "allowed proof fragments"):
            rejected.give(unchanged, outside.suffix)
        self.assertEqual(rejected.handle, unchanged)

    def test_e_checks_and_applies_the_exact_term(self):
        executable = os.environ.get("ITPEVAL_REAL_E_EXECUTABLE")
        self.check_replay_and_policy(prepare_solver("e", executable=Path(executable) if executable else None,
                                                  prefix=self.prefix))

    @skipUnless(os.environ.get("ITPEVAL_REAL_VAMPIRE_EXECUTABLE"), "requires a Vampire build that reports premise names")
    def test_vampire_checks_and_applies_the_exact_term(self):
        executable = Path(os.environ["ITPEVAL_REAL_VAMPIRE_EXECUTABLE"])
        self.check_replay_and_policy(prepare_solver("vampire", executable=executable, prefix=self.prefix))

    def test_ground_scope_omits_dependent_equality_elimination(self):
        task, prepared = self.prepare(manifest="transport.json")
        receipt = run_agda_horn_search(task, prepared=prepared)
        self.assertEqual(receipt.observation.goal, "B")
        self.assertEqual(receipt.problem.hypotheses, (AgdaHornHypothesis("proof", (), "A"),))
        self.assertIn("equal", receipt.observation.skipped_bindings)
        self.assertEqual(receipt.search.native_status, "CounterSatisfiable")
        self.assertIsNone(receipt.suffix)
        self.assertIsNone(receipt.replay)

        session = AgdaHoleSession(task, prepared)
        handle, _ = session.give(session.handle, "transport A B equal proof")
        self.assertTrue(session.finalize(handle).task_success)

    def test_unsupported_goal_is_observed_and_does_not_reach_a_solver(self):
        task, prepared = self.prepare(self.fixture.parent / "auto", "right-zero.json")
        observation = observe_agda_horn(task, prepared=prepared)
        self.assertEqual(observation.goal, "n + 0 ≡ n")
        self.assertIsNone(observation.problem)
        with self.assertRaisesRegex(ValueError, "no supported local Horn problem"):
            run_agda_horn_search(task, prepared=prepared)

    def test_horn_observes_and_replays_an_all_multiline_slot(self):
        project = copytree(self.fixture, self.root / "multiline")
        manifest = project / "completion.json"
        policy = json.loads(manifest.read_bytes())
        generated, reference = policy["allowed_edits"]
        term = generated.removeprefix("= ")
        expected = "=\n  " + term
        policy["allowed_edits"] = [reference, expected]
        manifest.write_text(json.dumps(policy), encoding="utf-8")
        task, prepared = self.prepare(project)

        receipt = run_agda_horn_search(task, prepared=prepared)
        self.assertEqual(receipt.replay_outcome, "accepted")
        self.assertEqual(receipt.candidate, expected)
        self.assertEqual(receipt.suffix, term)
        session = AgdaHoleSession(task, prepared)
        handle, _ = session.give(session.handle, receipt.suffix)
        self.assertEqual(handle.revision, 1)
        self.assertTrue(session._filled(session.inspect(handle)))
        final = session.finalize(handle)
        self.assertTrue(final.task_success)
        self.assertEqual(final.artifact_id, receipt.replay.artifact_id)
