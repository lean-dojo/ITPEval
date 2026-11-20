"""Check batched ACL2 and Metamath action restoration with native provers."""

from dataclasses import replace
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from unittest import TestCase, skipUnless
from unittest.mock import patch

from itpeval.backends.registry import curated_project, get_backend
from itpeval.environments import prepare_project
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


@skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed ACL2 and Metamath")
class ActionRestoreTests(TestCase):
    def setUp(self):
        directory = TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.prefix = Path(os.environ["ITPEVAL_REAL_PREFIX"])

    def prepare(self, prover, project):
        prepared = prepare_project(prover, project, cache=self.root / "cache", prefix=self.prefix)
        backend = get_backend(prover)
        return backend, prepared, backend.build_task(prepared)

    def test_batch_uses_one_native_transaction_and_validates_each_saved_state(self):
        cases = {
            "acl2": (NativeProofAction("command", "s"), NativeProofAction("command", "undo"),
                     NativeProofAction("command", "s"), NativeProofAction("command", "top")),
            "metamath": tuple(NativeProofAction("assign", label, step_index=index)
                              for index, label in ((1, "distinct"), (1, "vx"), (2, "vy"), (2, "vx"))),
        }
        for prover, sequence in cases.items():
            with self.subTest(prover=prover):
                *actions, wrong = sequence
                project = curated_project(prover)
                if prover == "acl2":
                    project = project.parent / "interaction"
                backend, prepared, task = self.prepare(prover, project)
                driver = NativeProofDriver(task, prepared)
                expected = [driver.observe()]
                for action in actions[:2]:
                    transition = driver.advance(action)
                    self.assertTrue(transition.committed)
                    expected.append(transition.observation)
                rejected = driver.advance(wrong)
                self.assertFalse(rejected.committed)
                self.assertEqual(rejected.observation.state_id, expected[-1].state_id)
                partial = driver.checkpoint()
                transition = driver.advance(actions[-1])
                self.assertTrue(transition.committed)
                expected.append(transition.observation)
                checkpoint = driver.checkpoint()

                session = backend.open_native_session(task, prepared=prepared)

                def payload(sequence):
                    if prover == "acl2":
                        return (action.text for action in sequence)
                    return ((action.step_index, action.text) for action in sequence)

                initial_handle = session.handle
                with self.assertRaisesRegex(ValueError, "replay step 3") as error:
                    session.replay_prefix(initial_handle, payload([*actions[:2], wrong, actions[-1]]))
                self.assertIn(rejected.observation.native["diagnostic"], str(error.exception))
                self.assertEqual(session.handle, initial_handle)
                self.assertIsNone(session.candidate)
                cancelled = Event()
                cancelled.set()
                with self.assertRaisesRegex(RuntimeError, "cancelled"):
                    session.replay_prefix(initial_handle, payload(actions), cancel=cancelled)
                self.assertEqual(session.handle, initial_handle)

                with patch.object(session, "_run", wraps=session._run) as run:
                    observed = session.replay_prefix(initial_handle, payload(actions))
                    self.assertEqual([state.to_dict() for state in observed], [state.native for state in expected])
                    self.assertEqual(session.handle.revision, len(actions))
                    self.assertEqual(session.inspect(session.handle), observed[-1])
                    run.assert_called_once()

                restored = NativeProofDriver.from_checkpoint(task, prepared, checkpoint)
                self.assertEqual(restored.checkpoint(), checkpoint)
                result = restored.finalize()
                self.assertIs(result.evidence.task_success, True)
                self.assertEqual(result.candidate, session.candidate)

                continued = NativeProofDriver.from_checkpoint(task, prepared, partial)
                self.assertEqual(continued.advance(wrong), rejected)
                self.assertEqual(continued.checkpoint(), partial)
                self.assertEqual(continued.advance(actions[-1]).observation, expected[-1])
                self.assertEqual(continued.checkpoint(), checkpoint)

                tampered = replace(checkpoint, state_ids=(checkpoint.state_ids[0], "0" * 64, *checkpoint.state_ids[2:]))
                with self.assertRaisesRegex(ValueError, "differ"):
                    NativeProofDriver.from_checkpoint(task, prepared, tampered)

    def test_metamath_restored_ready_state_still_needs_distinct_variable_check(self):
        original = curated_project("metamath")
        project = self.root / "disjoint"
        project.mkdir()
        source = (original / "hello.mm").read_text()
        manifest = json.loads((original / "completion.json").read_bytes())
        anchor = manifest["anchor"]
        changed = anchor.replace("|- pair x y", "|- pair x x").replace("vx vy distinct", "vx vx distinct")
        (project / "hello.mm").write_text(source.replace(anchor, changed))
        manifest.update(anchor=changed, statement="|- pair x x", proof_slot="vx vx distinct",
                        allowed_edits=["vx vx distinct"])
        (project / "completion.json").write_text(json.dumps(manifest))
        _, prepared, task = self.prepare("metamath", project)
        driver = NativeProofDriver(task, prepared)
        for index, label in ((1, "distinct"), (1, "vx"), (2, "vx")):
            self.assertTrue(driver.advance(NativeProofAction("assign", label, step_index=index)).committed)
        restored = NativeProofDriver.from_checkpoint(task, prepared, driver.checkpoint())
        self.assertEqual(restored.observe().status, "ready")
        final = restored.finalize()
        self.assertEqual(final.candidate, "vx vx distinct")
        self.assertIs(final.evidence.task_success, False)
        self.assertIn("disjoint variable", final.evidence.stdout.lower())
