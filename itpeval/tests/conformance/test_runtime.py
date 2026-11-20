from dataclasses import replace
import json
import os
from pathlib import Path
import sys
import tempfile
from threading import Event, Thread
import time
import unittest

from itpeval.backends.registry import curated_task, prover_ids
from itpeval.core.types import Artifact, TaskSpec
from itpeval.runtime.process import run_process, task_environment
from itpeval.verification.policies import assemble


class ContractTests(unittest.TestCase):
    def test_roundtrip_identity_and_boundaries(self):
        for prover in prover_ids():
            with self.subTest(prover=prover):
                task = curated_task(prover, "fixture")
                self.assertEqual(task, TaskSpec.from_dict(json.loads(json.dumps(task.to_dict()))))
                self.assertNotEqual(task.task_id, replace(task, environment_id="other").task_id)
                assembled = assemble(task, task.allowed_edits[0])
                region = task.editable_regions[0]
                original = {item.path: item.data for item in task.artifact.files}
                updated = {item.path: item.data for item in assembled.files}
                actual = updated.pop(region.path)
                expected = original.pop(region.path)
                self.assertEqual(expected[:region.start] + task.allowed_edits[0].encode()
                                 + expected[region.end:], actual)
                self.assertEqual(original, updated)
                for edit in ("", "sorry", "replace target", "change context"):
                    with self.assertRaises(ValueError):
                        assemble(task, edit)

    def test_qualified_capability_requires_the_exact_environment_and_build(self):
        from types import SimpleNamespace
        from itpeval.backends.registry import require_capabilities
        with tempfile.TemporaryDirectory() as tmp:
            report = Path(tmp) / "report.jsonl"
            row = {"prover": "agda", "environment_id": "A", "prover_build": "build1",
                   "operation": "refine_hole", "status": "implemented/tested"}
            report.write_text(json.dumps(row) + "\n")
            spec = SimpleNamespace(prover="agda", prover_build="build1")
            env = SimpleNamespace(spec=spec, environment_id="A", extra_inputs=(), validate=lambda: None)
            opts = dict(prepared=env, qualification_report=report, allow_experimental=False)
            selected, = require_capabilities("agda", ["refine_hole"], **opts)
            self.assertEqual(selected.status, "implemented/tested")
            for name, build in [("B", "build1"), ("A", "build2")]:
                env.environment_id, env.spec.prover_build = name, build
                with self.assertRaises(NotImplementedError):
                    require_capabilities("agda", ["refine_hole"], **opts)

    def test_new_compositions(self):
        samples = {"metamath": "vy vx duplicate", "rocq": "intro p; assumption.",
                   "lean4": "rfl <;> simp", "hol4": "ALL_TAC THEN PROVE_TAC []",
                   "pvs": "(then (assert) (grind))"}
        for prover, example in samples.items():
            task = curated_task(prover, "fixture")
            self.assertNotIn(example, task.allowed_edits)
            self.assertTrue(assemble(task, example).artifact_id)
            with self.assertRaises(ValueError):
                assemble(task, example + "\nend")

    def test_native_proof_command_replay_uses_the_authorized_atoms(self):
        rocq = curated_task("rocq", "fixture")
        self.assertTrue(assemble(rocq, "intro p.\nassumption.").artifact_id)
        with self.assertRaises(ValueError):
            assemble(rocq, "intro p.\nAbort.")

        acl2 = replace(curated_task("acl2", "fixture"), proof_atoms=(":demote", ":s"))
        self.assertTrue(assemble(acl2, ":instructions (:demote :s)").artifact_id)
        with self.assertRaises(ValueError):
            assemble(acl2, ":instructions (:skip-proofs :s)")

    def test_hol_tactic_tree_checks_each_leaf_against_the_reviewed_vocabulary(self):
        for prover, separator in (("hol4", ", "), ("hol-light", "; ")):
            with self.subTest(prover=prover):
                task = replace(curated_task(prover, "fixture"), proof_atoms=("A THEN B", "C", "D"))
                nested = f"((A THEN B) THENL [((C) THENL [D]){separator}D])"
                self.assertTrue(assemble(task, nested).artifact_id)
                for invalid in (nested[:-1], nested.replace(separator + "D", separator + "E"),
                                nested.replace(separator + "D", " ;, D"), "((C) THENL [])"):
                    with self.assertRaises(ValueError):
                        assemble(task, invalid)

    def test_artifact_path_and_digest_integrity(self):
        for name in ("../escaped", "/escaped", "alias/../a", "./a"):
            with self.assertRaises(ValueError):
                Artifact.from_files(name, {name: b"abc"})
        artifact = Artifact.from_files("source", {"source": bytes(range(256))})
        record = artifact.to_dict()
        record["files"][0]["sha256"] = "mismatched"
        with self.assertRaises(ValueError):
            Artifact.from_dict(record)


class ProcessTests(unittest.TestCase):
    def test_buffer_and_stdin(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "input"
            path.write_text("X" * 9999 + "Z")
            p = run_process(["cat"], stdin_path=path, max_log_bytes=5)
        self.assertEqual((p.outcome, p.stdout, p.truncated), ("exited", "XXXXZ", True))

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux subreaper required")
    def test_cancellation_reaps_detached_descendants(self):
        with tempfile.TemporaryDirectory() as tmp:
            ready = Path(tmp) / "pid"
            cancel = Event()
            result = []
            script = ("import os,sys,time; pid=os.fork(); "
                      "os.setsid() if pid==0 else None; "
                      "open(sys.argv[1],'w').write(str(os.getpid())) if pid==0 else None; time.sleep(30)")
            thread = Thread(target=lambda: result.append(run_process(
                [sys.executable, "-c", script, str(ready)], cancel=cancel, timeout_s=3)))
            thread.start()
            try:
                for _ in range(100):
                    if ready.exists() and ready.read_text():
                        break
                    time.sleep(.02)
                child = int(ready.read_text())
            finally:
                cancel.set()
                thread.join(5)
            self.assertFalse(thread.is_alive())
            self.assertEqual(result[0].outcome, "cancelled")
            self.assertFalse(Path(f"/proc/{child}").exists())

    def test_timeout_and_selection(self):
        result = run_process([sys.executable, "-c", "import time;time.sleep(10)"], timeout_s=.2)
        self.assertEqual(result.outcome, "timeout")
        self.assertEqual(task_environment({"ITPEVAL_TASK_FILE":"stale","ITPEVAL_OPERATION":"statement"}), {})


class ProjectTaskTests(unittest.TestCase):
    def test_existing_declaration_and_binders_are_preserved(self):
        from types import SimpleNamespace
        from itpeval.backends.projects import build_task
        from itpeval.backends.registry import curated_project

        for prover in prover_ids():
            with self.subTest(prover=prover):
                root = curated_project(prover)
                m = json.loads((root / "completion.json").read_text())
                prepared = SimpleNamespace(project=root, spec=SimpleNamespace(prover=prover),
                                           environment_id="test")
                task = build_task(prepared)
                source = (root / task.artifact.entrypoint).read_bytes()
                anchor = m["anchor"].encode()
                slot = m["proof_slot"].encode()
                start = source.index(anchor) + anchor.index(slot)
                self.assertEqual(task.editable_regions[0].start, start)
                candidate = task.allowed_edits[1]
                final = {entry.path: entry.data for entry in assemble(task, candidate).files}
                after = final[task.artifact.entrypoint]
                # Strip only the new target observer. Remaining bytes should differ
                # from the original by exactly the submitted proof fragment.
                observer = (m.get("observer_anchor") or m["anchor"]).encode()
                at = source.index(observer) + len(observer) - len(slot) + len(candidate.encode())
                expected = source[:start] + candidate.encode() + source[start + len(slot):]
                added = len(after) - len(expected)
                self.assertEqual(after[:at] + after[at + added:], expected)
                if prover == "lean4":
                    self.assertIn(b"theorem itpeval_target (x : Nat) : x = x", after)

    def test_admissions_fail_even_when_listed(self):
        for prover, admission in (("lean4", "sorry"), ("rocq", "Admitted."), ("metamath", "?"),
                                 ("isabelle", "sorry"), ("agda", "{! !}"), ("mizar", "::$P-")):
            task = curated_task(prover, "test")
            task = replace(task, allowed_edits=(*task.allowed_edits, admission))
            with self.assertRaises(ValueError):
                assemble(task, admission)

    def test_unwitnessed_secondary_obligation(self):
        from types import SimpleNamespace
        from itpeval.backends.projects import build_task
        from itpeval.backends.registry import curated_project
        import shutil
        for prover in set(prover_ids()) - {"pvs"}:
            with self.subTest(prover=prover), tempfile.TemporaryDirectory() as tmp:
                shutil.copytree(curated_project(prover), tmp, dirs_exist_ok=True)
                path = Path(tmp) / "completion.json"
                data = json.loads(path.read_text())
                data["obligations"] = ["anUnverifiedDeclaration"]
                path.write_text(json.dumps(data))
                prepared = SimpleNamespace(project=Path(tmp), spec=SimpleNamespace(prover=prover),
                                           environment_id="test")
                with self.assertRaisesRegex(ValueError, "secondary obligations"):
                    build_task(prepared)

    def test_rocq_mixed_assumption_reports(self):
        from itpeval.verification.service import _reported_assumptions
        task = curated_task("rocq", "test")
        self.assertEqual(_reported_assumptions(task, "Closed under the global context\nAxioms:\nfact : False\n"),
                         {"fact"})

    def test_schema_bundle_is_current(self):
        from itpeval.core import schema
        path = Path(schema.__file__).with_name("schemas.json")
        self.assertEqual(json.loads(path.read_text()), schema.schemas())


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "set ITPEVAL_REAL_PREFIX to run native checks")
class LeanTrustTests(unittest.TestCase):
    def test_unsupported_kernel_options_do_not_receive_proof_credit(self):
        from itpeval.backends.registry import curated_project
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify
        with tempfile.TemporaryDirectory() as tmp:
            env = prepare_project("lean4", curated_project("lean4"), prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                  cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", tmp)), options={"debug.skipKernelTC": "true"})
            task = curated_task("lean4", env.environment_id)
            evidence = verify(task, "rfl", prepared=env)
            self.assertEqual(evidence.execution_outcome, "unsupported_operation")
            self.assertIsNone(evidence.task_success)

    def test_metamath_axiom_policy(self):
        from itpeval.backends.registry import curated_project
        from itpeval.backends.projects import build_task
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify
        import shutil
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "project"
            shutil.copytree(curated_project("metamath"), root)
            manifest = root / "completion.json"
            data = json.loads(manifest.read_text())
            data["allowed_assumptions"] = ["distinct"]
            manifest.write_text(json.dumps(data))
            env = prepare_project("metamath", root, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                  cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", Path(tmp) / "cache")))
            task = build_task(env)
            self.assertIs(verify(task, "vx vy distinct", prepared=env).task_success, True)
            evidence = verify(task, "vx vy duplicate", prepared=env)
            self.assertIs(evidence.task_success, False, evidence.to_dict())
            self.assertIn("Unauthorized Metamath axioms: duplicate", evidence.stderr)

    def test_rocq_assumptions_with_unrelated_closed_declaration(self):
        from itpeval.backends.projects import CompletionManifest, build_task
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp) / "project"
            project.mkdir()
            target = "Theorem requested : True. Proof. exact I. Qed."
            (project / "Goal.v").write_text(
                "Axiom extra : True.\nLemma unrelated : True. Proof. exact I. Qed.\n"
                "Print Assumptions unrelated.\n" + target + "\n")
            for allowed in [(), ("extra",)]:
                manifest = CompletionManifest("Goal.v", ("Goal.v",), target, "requested", "True", "exact I.",
                                              ("exact I.", "exact extra."), allowed_assumptions=allowed)
                (project / "completion.json").write_text(json.dumps(manifest.to_dict()))
                env = prepare_project("rocq", project, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                      cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", Path(tmp) / "cache")))
                evidence = verify(build_task(env), "exact extra.", prepared=env)
                self.assertIs(evidence.task_success, bool(allowed), evidence.to_dict())

    def test_transitive_dependencies_and_declared_assumptions(self):
        from itpeval.backends.projects import CompletionManifest, build_task
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "project"
            root.mkdir()
            target = "theorem requested : True := by\n  exact True.intro"
            (root / "Hello.lean").write_text(
                "axiom projectParameter : True\n"
                "theorem incompleteDependency : True := by sorry\n" + target + "\n")
            for assumptions in [(), ("projectParameter", "sorryAx")]:
                manifest = CompletionManifest(
                    entrypoint="Hello.lean", files=("Hello.lean",), anchor=target, target="requested",
                    statement="True", proof_slot="exact True.intro",
                    allowed_edits=("exact True.intro", "exact projectParameter", "exact incompleteDependency", "sorry"),
                    allowed_assumptions=assumptions)
                (root / "completion.json").write_text(json.dumps(manifest.to_dict()))
                prepared = prepare_project("lean4", root, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                           cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", Path(tmp) / "cache")))
                task = build_task(prepared)
                for candidate, wanted in zip(task.allowed_edits, (True, bool(assumptions), False, False)):
                    with self.subTest(assumptions=assumptions, candidate=candidate):
                        evidence = verify(task, candidate, prepared=prepared)
                        self.assertIs(evidence.task_success, wanted, evidence.to_dict())


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "set ITPEVAL_REAL_PREFIX to run native checks")
class LocalImportTests(unittest.TestCase):
    def test_custom_entrypoints_and_source_dependencies(self):
        from itpeval.backends.projects import CompletionManifest, build_task
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify

        fixtures = [
            ("lean4", "Library.lean", "theorem localFact : True := True.intro",
             "Goal.lean", "import Library\n", "theorem requested : True := by\n  exact localFact", "exact localFact"),
            ("rocq", "Library.v", "Lemma localFact : True. Proof. exact I. Qed.",
             "Goal.v", "Require Import Library.\n", "Theorem requested : True. Proof. exact localFact. Qed.", "exact localFact."),
        ]
        for prover, lib, content, main, imports, decl, term in fixtures:
            with self.subTest(prover=prover), tempfile.TemporaryDirectory() as tmp:
                project = Path(tmp) / "project"
                project.mkdir()
                (project / lib).write_text(content + "\n")
                (project / main).write_text(imports + decl + "\n")
                manifest = CompletionManifest(main, (main, lib), decl, "requested", "True", term,
                                              (term,), dependency_sources=(lib,))
                (project / "completion.json").write_text(json.dumps(manifest.to_dict()))
                prepared = prepare_project(prover, project, prefix=Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                                           cache=Path(os.environ.get("ITPEVAL_REAL_CACHE", Path(tmp) / "cache")))
                ev = verify(build_task(prepared), term, prepared=prepared)
                self.assertIs(ev.task_success, True, ev.to_dict())
                self.assertEqual(set(p.name for p in project.iterdir()), {main, lib, "completion.json"})


class PoolTests(unittest.TestCase):
    def test_job_input_is_consumed_within_queue_limit(self):
        from unittest.mock import patch
        from itpeval.runtime.scheduler import Job, run_jobs
        task = curated_task("lean4", "e")
        pulled = []
        def jobs():
            for i in range(100):
                pulled.append(i)
                yield Job(task, "rfl", None)
        with patch("itpeval.runtime.scheduler.verify", return_value="checked"):
            run = run_jobs(jobs(), workers=1, queue_limit=2)
            self.assertEqual(next(run), (0, "checked"))
            self.assertEqual(len(pulled), 2)
            run.close()

    def test_scheduler_rotates_provers_and_environments_and_keeps_writer_order(self):
        from threading import get_ident
        from unittest.mock import patch
        from itpeval.runtime.scheduler import Job, run_jobs

        lean_a = curated_task("lean4", "a")
        lean_b = curated_task("lean4", "b")
        rocq = curated_task("rocq", "c")
        jobs = [Job(task, str(index), None) for index, task in enumerate(
            (lean_a, lean_a, lean_a, rocq, lean_b, lean_b))]
        caller = get_ident()
        written = []

        def writer(index, evidence):
            written.append((index, evidence, get_ident()))

        with patch("itpeval.runtime.scheduler.verify", side_effect=lambda task, candidate, **kwargs: candidate):
            results = list(run_jobs(jobs, workers=1, queue_limit=6, writer=writer))
        self.assertEqual([i for i, _ in results], [0, 3, 4, 1, 5, 2])
        self.assertEqual(written, [(i, evidence, caller) for i, evidence in results])

    def test_interleave_jobs_pulls_lazily_from_each_source(self):
        from itpeval.runtime.scheduler import interleave_jobs

        pulled = []

        def source(name, size):
            for index in range(size):
                item = name, index
                pulled.append(item)
                yield item

        result = interleave_jobs(source("lean4", 3), source("rocq", 0), source("metamath", 1))
        self.assertEqual(pulled, [])
        self.assertEqual(next(result), ("lean4", 0))
        self.assertEqual(pulled, [("lean4", 0)])
        self.assertEqual(list(result), [("metamath", 0), ("lean4", 1), ("lean4", 2)])

    def test_per_prover_limit_and_failed_worker_recovery(self):
        from threading import Lock, get_ident
        from unittest.mock import patch
        from itpeval.core.types import VerificationEvidence
        from itpeval.runtime.scheduler import Job, run_jobs

        task = curated_task("lean4", "env")
        active = maximum = 0
        lock = Lock()
        writer_thread = get_ident()
        writes = []

        def checker(t, candidate, **kwargs):
            nonlocal active, maximum
            with lock:
                active += 1
                maximum = max(maximum, active)
            try:
                if candidate == "crash":
                    raise RuntimeError("worker failed")
                time.sleep(.02)
                return VerificationEvidence(t.task_id, t.environment_id, t.artifact.artifact_id,
                                            "exited", "accepted", True, "preserved", "proved")
            finally:
                with lock:
                    active -= 1

        jobs = [Job(task, candidate, None) for candidate in ("good", "crash", "good")]
        with patch("itpeval.runtime.scheduler.verify", checker):
            outcomes = dict(run_jobs(jobs, workers=3, prover_limits={"lean4": 1},
                                     writer=lambda i, result: writes.append((i, get_ident()))))
        self.assertEqual(maximum, 1)
        self.assertEqual(outcomes[1].execution_outcome, "backend_error")
        self.assertIsNone(outcomes[1].task_success)
        self.assertIs(outcomes[2].task_success, True)
        self.assertEqual({(i, writer_thread) for i in range(3)}, set(writes))


class RuntimeAuditRegressions(unittest.TestCase):
    def test_cancellation_stops_consuming_new_jobs(self):
        from unittest.mock import patch
        from itpeval.runtime.pool import cancelled_evidence
        from itpeval.runtime.scheduler import Job, run_jobs
        signal = Event()
        task = curated_task("metamath", "test")
        pulled = []
        def source():
            for i in range(10):
                pulled.append(i)
                yield Job(task, "x", None)
        def stop(*args, **kwargs):
            signal.set()
            return cancelled_evidence(task)
        with patch("itpeval.runtime.scheduler.verify", side_effect=stop) as checker:
            rows = list(run_jobs(source(), workers=1, queue_limit=2, cancel=signal))
        self.assertEqual(pulled, [0, 1])
        self.assertEqual(rows, [(0, cancelled_evidence(task)), (1, cancelled_evidence(task))])
        checker.assert_called_once()

    def test_cancellation_during_admission_does_not_start_a_checker(self):
        from unittest.mock import patch
        from itpeval.runtime.pool import cancelled_evidence
        from itpeval.runtime.scheduler import Job, run_jobs

        signal = Event()
        task = curated_task("metamath", "admission")

        def source():
            signal.set()
            yield Job(task, "x", None)
            self.fail("the input iterator was advanced after cancellation")

        with patch("itpeval.runtime.scheduler.verify") as checker:
            rows = list(run_jobs(source(), workers=2, queue_limit=4, cancel=signal))
        self.assertEqual(rows, [(0, cancelled_evidence(task))])
        checker.assert_not_called()

    def test_source_locator_requires_complete_native_statement(self):
        from types import SimpleNamespace
        import shutil
        from itpeval.backends.projects import build_task
        from itpeval.backends.registry import curated_project
        for prover in ("isabelle", "metamath", "pvs", "mizar", "acl2", "agda"):
            with self.subTest(prover=prover), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)/"project"
                shutil.copytree(curated_project(prover), root)
                p = root/"completion.json"
                m = json.loads(p.read_bytes())
                # Each candidate string occurs in the source but fails to describe
                # the complete proposition. Isabelle's single identifier uses an
                # extended source statement so this regression tests the boundary.
                if prover == "isabelle":
                    m["anchor"] = m["anchor"].replace("itpeval_target: p", "itpeval_target: p ∧ p")
                    entry = root/m["entrypoint"]
                    entry.write_text(entry.read_text().replace("itpeval_target: p", "itpeval_target: p ∧ p"))
                else:
                    m["statement"] = m["statement"][:len(m["statement"])//2]
                p.write_text(json.dumps(m))
                env = SimpleNamespace(project=root, spec=SimpleNamespace(prover=prover), environment_id="test")
                with self.assertRaisesRegex(ValueError, "manifest statement"):
                    build_task(env)

    @unittest.skipUnless(sys.platform.startswith("linux"), "requires Linux prlimit")
    def test_native_cpu_budget_returns_resource_exhaustion(self):
        result = run_process([sys.executable, "-c", "while True: pass"], cpu_seconds=1, timeout_s=10)
        self.assertEqual(result.outcome, "resource_exhausted")
        self.assertGreater(result.cpu_time_s, 0.5)

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux guardian metrics")
    def test_signal_and_launcher_failure_are_distinguished(self):
        executable = "/itpeval-fixture/missing-native-executable"
        no_tool = run_process([executable], timeout_s=5)
        self.assertEqual((no_tool.outcome, no_tool.returncode), ("unavailable_environment", 127))
        killed = run_process([sys.executable, "-c", "import os,signal;os.kill(os.getpid(), signal.SIGTERM)"],
                             timeout_s=5)
        self.assertEqual((killed.outcome, killed.returncode), ("crash", 143))
        ordinary = run_process([sys.executable, "-c", "raise SystemExit(143)"], timeout_s=5)
        self.assertEqual((ordinary.outcome, ordinary.returncode), ("exited", 143))


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires installed native provers")
class VerifiedBaseTests(unittest.TestCase):
    def test_legacy_facade_supervised_resources_and_cancellation(self):
        from itpeval.core.types import Budgets
        from itpeval.itp import run_itp
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "demo.mm").write_text("$c wff $. $v x $. vx $f wff x $. id $p wff x $= vx $.\n")
            options = {"prover": "metamath", "task_dir": root, "prefix": Path(os.environ["ITPEVAL_REAL_PREFIX"]),
                       "budgets": Budgets(timeout_s=5, max_log_bytes=32, cpu_seconds=5)}
            completed = run_itp(**options)
            self.assertTrue(completed.ok)
            self.assertTrue(completed.logs_truncated)
            self.assertLessEqual(len(completed.stdout.encode()), 32)
            signal = Event()
            signal.set()
            stopped = run_itp(**options, cancel=signal)
            self.assertFalse(stopped.ok)
            self.assertEqual(stopped.execution_outcome, "cancelled")

    def test_reuse_requires_identical_verified_includes_and_single_extension(self):
        from itpeval.backends.projects import CompletionManifest, build_task
        from itpeval.backends.metamath.base import BaseVerificationError, prepare_base
        from itpeval.environments import prepare_project
        from itpeval.verification.service import verify
        prefix = Path(os.environ["ITPEVAL_REAL_PREFIX"])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)/"project"
            root.mkdir()
            base = root/"base.mm"
            base.write_text("$c wff $. $v x $. vx $f wff x $. base-id $p wff x $= vx $.\n")
            client = root/"client.mm"
            stmt = "want $p wff x $= vx $."
            client.write_text("$[ base.mm $]\n"+stmt+"\n")
            m = CompletionManifest("client.mm", ("base.mm", "client.mm"), stmt, "want", "wff x", "vx", ("vx",))
            (root/"completion.json").write_text(json.dumps(m.to_dict()))
            def prepare():
                return prepare_project("metamath", root, prefix=prefix, cache=Path(tmp)/"cache")
            env = prepare()
            first, again = prepare_base(env, "base.mm"), prepare_base(env, "base.mm")
            self.assertFalse(first.cache_hit)
            self.assertEqual((again.cache_hit, again.base_id), (True, first.base_id))
            proof = verify(build_task(env), "vx", prepared=env, metamath_base="base.mm")
            self.assertIs(proof.task_success, True, proof.to_dict())
            client.write_text("$[ base.mm $]\nother $p wff x $= vx $.\n"+stmt+"\n")
            other = prepare()
            self.assertEqual(verify(build_task(other), "vx", prepared=other,
                                    metamath_base="base.mm").execution_outcome, "unsupported_operation")
            base.write_text(base.read_text().replace("base-id $p wff x $= vx", "base-id $p wff x $= ?"))
            broken = prepare()
            with self.assertRaises(BaseVerificationError):
                prepare_base(broken, "base.mm")
            result = verify(build_task(broken), "vx", prepared=broken, metamath_base="base.mm")
            self.assertIsNone(result.task_success)
            self.assertEqual(result.execution_outcome, "unavailable_environment")
