"""Keep rejected native commands replayable without treating them as full proofs."""

import json
import os
import unittest
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event

from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl, read_jsonl
from itpeval.environments import prepare_project
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import (NativeProofEpisode, SearchWithATP, check_native_episode,
                                            replay_native_episode, rollout_native)
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed Rocq")
class NativeProofEpisodeTests(unittest.TestCase):
    def test_checkpoint_and_training_preserve_the_state_after_a_rejected_command(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            env = prepare_project("rocq", curated_project("rocq"), cache=root / "cache",
                                  prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
            task = get_backend("rocq").build_task(env)
            manifest = RunManifest.for_native_proof_task(task, "native-test", "native-test", {}, max_attempts=3)
            commands = ("exact I.", "intro p.", "exact p.")
            episode = rollout_native(task, env, manifest,
                                     lambda _, __, history: NativeProofAction("command", commands[len(history)]))
            loaded = NativeProofEpisode.from_dict(json.loads(json.dumps(episode.to_dict())))
            self.assertTrue(check_native_episode(loaded).task_success)
            self.assertTrue(replay_native_episode(loaded, task=task, prepared=env).task_success)
            self.assertEqual([step.committed for step in episode.transitions], [False, True, True])

            driver = NativeProofDriver(task, env)
            driver.advance(episode.transitions[1].action)
            saved = driver.checkpoint()
            tampered = replace(saved, state_ids=(saved.state_ids[0], "0" * 64))
            with self.assertRaisesRegex(ValueError, "replay step 1"):
                NativeProofDriver.from_checkpoint(task, env, tampered)

            episodes_file = root / "episodes.jsonl"
            output = root / "training"
            jsonl(episodes_file, [loaded.to_dict()])
            report = export_training_data(output, native_episodes=[episodes_file])
            self.assertEqual(report["views"]["proof_steps"], 3)
            rows = list(read_jsonl(output / "proof_steps.jsonl"))
            self.assertEqual([row["reward"] for row in rows], [None, None, 1.0])
            self.assertEqual(rows[0]["before"], rows[1]["before"])
            self.assertEqual(rows[0]["feedback"]["status"], "rejected")
            self.assertIsNone(rows[0]["final_evidence"])
            self.assertTrue(rows[-1]["terminated"])

    @unittest.skipUnless(os.environ.get("ITPEVAL_REAL_ATP_PREFIX"), "requires installed ATP components")
    def test_solver_receipt_is_bound_to_the_native_revision_that_asked_for_it(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = curated_project("rocq").parent / "horn-prefix"
            env = prepare_project("rocq", fixture, cache=root / "cache",
                                  prefix=Path(os.environ["ITPEVAL_REAL_ATP_PREFIX"]))
            task = get_backend("rocq").build_task(env)
            manifest = RunManifest.for_native_proof_task(task, "native-test", "hybrid-test", {}, max_attempts=2)
            decisions = (NativeProofAction("command", "intro hp."), SearchWithATP())
            episode = rollout_native(task, env, manifest, lambda _task, _state, history: decisions[len(history)])
            self.assertEqual(episode.atp.outcome, "accepted")
            self.assertTrue(replay_native_episode(episode, task=task, prepared=env).task_success)

            tampered = replace(episode, atp=replace(episode.atp, checkpoint_id="0" * 64))
            with self.assertRaisesRegex(ValueError, "proof revision"):
                check_native_episode(tampered)
            unresolved = rollout_native(task, env, manifest, lambda _task, _state, _history: SearchWithATP())
            self.assertEqual((unresolved.stop_reason, unresolved.atp.outcome, unresolved.transitions),
                             ("atp_unresolved", "unsupported_goal", ()))
            self.assertIsNone(replay_native_episode(unresolved, task=task, prepared=env))

            path = root / "examples.jsonl"
            output = root / "training"
            jsonl(path, [episode.to_dict()])
            export_training_data(output, native_episodes=(path,))
            rows = list(read_jsonl(output / "proof_steps.jsonl"))
            self.assertIsNone(rows[0]["atp_json"])
            self.assertEqual(json.loads(rows[-1]["atp_json"])["checkpoint_id"], episode.atp.checkpoint_id)

    def test_hol_subgoal_automation_records_progress_without_a_proof_reward(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = curated_project("hol4").parent / "metis"
            env = prepare_project("hol4", fixture, cache=root / "cache", prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
            task = get_backend("hol4").build_task(env)
            manifest = RunManifest.for_native_proof_task(task, "native-test", "hol-automation", {}, max_attempts=4)
            decisions = (NativeProofAction("tactic", "REPEAT DISCH_TAC", ()),
                         NativeProofAction("tactic", "CONJ_TAC", (0,)),
                         SearchWithATP(goal_path=(0, 1)), SearchWithATP(goal_path=(0, 0)))
            episode = rollout_native(task, env, manifest, lambda _task, _state, history: decisions[len(history)])
            saved, = episode.atp_progress
            self.assertEqual(saved.step, 2)
            self.assertEqual(saved.suggestion.outcome, "progress")
            self.assertIsNone(saved.suggestion.verification)
            self.assertTrue(replay_native_episode(episode, task=task, prepared=env).task_success)

            driver = NativeProofDriver(task, env)
            for transition in episode.transitions[:2]:
                driver.advance(transition.action)
            checkpoint = driver.checkpoint()
            suggestion = saved.suggestion
            after = suggestion.evidence.after
            forged = replace(suggestion, evidence=replace(suggestion.evidence, after=replace(
                after, goals=(replace(after.goals[0], conclusion="changed"),))))
            with self.assertRaisesRegex(ValueError, "reproduce"):
                driver.apply_atp(forged)
            self.assertEqual(driver.checkpoint(), checkpoint)

            path = root / "examples.jsonl"
            output = root / "training"
            jsonl(path, [episode.to_dict()])
            export_training_data(output, native_episodes=(path,))
            rows = list(read_jsonl(output / "proof_steps.jsonl"))
            self.assertEqual([row["reward"] for row in rows], [None, None, None, 1.0])
            self.assertEqual(json.loads(rows[2]["atp_json"])["outcome"], "progress")

    def test_metamath_search_honors_trial_limits_and_commits_one_assignment(self):
        with TemporaryDirectory() as directory:
            env = prepare_project("metamath", curated_project("metamath"), cache=Path(directory),
                                  prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
            task = get_backend("metamath").build_task(env)
            driver = NativeProofDriver(task, env)
            checkpoint = driver.checkpoint()

            limited = driver.suggest_atp(max_trials=1)
            self.assertEqual(limited.outcome, "trial_limit")
            self.assertEqual(len(limited.evidence.trials), 1)
            cancel = Event()
            cancel.set()
            self.assertEqual(driver.suggest_atp(cancel=cancel).outcome, "cancelled")
            self.assertEqual(driver.checkpoint(), checkpoint)

            suggestion = driver.suggest_atp()
            self.assertEqual(suggestion.outcome, "progress")
            self.assertEqual([move.text for move in suggestion.evidence.plan], ["distinct", "vx", "vy"])
            self.assertIsNone(suggestion.verification)
            self.assertTrue(suggestion.evidence.trials[-1].verification.task_success)
            self.assertTrue(driver.apply_atp(suggestion).committed)
            self.assertEqual(driver.checkpoint().actions, (suggestion.action,))

    def test_pvs_requires_separate_prooflite_for_a_multi_command_close(self):
        with TemporaryDirectory() as directory:
            project = curated_project("pvs").parent / "grind"
            env = prepare_project("pvs", project, cache=Path(directory), prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]))
            task = get_backend("pvs").build_task(env)
            driver = NativeProofDriver(task, env)
            for command in ("(skosimp)", "(split)"):
                driver.advance(NativeProofAction("command", command))
            driver.apply_atp(driver.suggest_atp())
            checkpoint = driver.checkpoint()
            self.assertEqual(driver.suggest_atp().outcome, "proof_fragment_required")
            self.assertEqual(driver.checkpoint(), checkpoint)

            fragment = "(then (skosimp) (split) (grind))"
            result = driver.suggest_atp(proof_fragment=fragment)
            self.assertEqual(result.evidence.finalization.match, "same_locked_target")
            self.assertEqual(dict(result.verification.obligations)["twice_TCC1"], "discharged")
            self.assertEqual(driver.apply_atp(result).observation.status, "ready")
