"""Exercise warm proof branches, local imports, and worker retirement on Linux."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from time import monotonic, sleep

from itpeval.backends.hol_light.worker import ForkedHOLLight
from itpeval.backends.hol_tactics import HOLProofSession
from itpeval.backends.projects import build_task
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.verification.service import verify


_DELAY = '''
let put_pid file =
  let path = Filename.concat (Filename.dirname (Sys.getenv "ITPEVAL_TRACE")) file in
  let handle = open_out path in
  Printf.fprintf handle "%d\\n" (Unix.getpid ()); close_out handle;;
let () =
  match Unix.fork () with
  | 0 -> ignore (Unix.setsid ()); put_pid "detached"; Unix.sleep 30; exit 0
  | _ -> put_pid "child"; Unix.sleep 30;;
'''


def _locked(name, prefix, cache):
    project = ROOT / "tests/fixtures/projects/hol-light" / name
    return prepare_project("hol-light", project, prefix=prefix, cache=cache)


def _job(root, name, source):
    work = root / name
    work.mkdir()
    (work / "run.ml").write_text(source, encoding="utf-8")
    return work


def _isolation(worker, task, project, root):
    first = _job(root, "mutate", 'let itpeval_child_binding = TRUTH;;\n'
                 'Unix.putenv "ITPEVAL_CHILD_PRIVATE" "canary";;\nload_path := [];;\n')
    second = _job(root, "check-binding", "let leak = itpeval_child_binding;;\n")
    third = _job(root, "check-environment",
                 'let () = assert (Sys.getenv_opt "ITPEVAL_CHILD_PRIVATE" = None && !load_path <> []);;\n')
    results = [worker._run(task, project, job, None) for job in (first, second, third)]
    return ([out.returncode for out in results] == [0, 1, 0]
            and "Unbound value itpeval_child_binding" in results[1].stdout + results[1].stderr)


def _retirement(worker, task, project, root, cancel=None):
    """Use an internal test job to create a detached descendant, then stop it."""
    child = _job(root, "active-child", _DELAY)
    paths = (child / "child", child / "detached")
    with ThreadPoolExecutor(max_workers=1) as pool:
        check = pool.submit(worker._run, task, project, child, cancel)
        deadline = monotonic() + min(8, task.budgets.timeout_s)
        while not all(path.is_file() and path.stat().st_size for path in paths):
            if check.done() or monotonic() >= deadline:
                if cancel is not None:
                    cancel.set()
                raise RuntimeError("request did not create the supervised test children")
            sleep(0.01)
        pids = [int(path.read_text()) for path in paths]
        if cancel is not None:
            cancel.set()
        result = check.result()
    return {"outcome": result.outcome, "worker_retired": not worker.active,
            "descendants_reaped": all(not Path(f"/proc/{pid}").exists() for pid in pids)}


def branching(prefix, root):
    project = _locked("interaction", prefix, root / "cache")
    task = build_task(project)
    started = monotonic()
    with ForkedHOLLight(project) as worker:
        startup = monotonic() - started
        session = HOLProofSession(task, project, worker=worker)
        start = monotonic()
        initial = session.inspect(session.handle)
        first_observation_s = monotonic() - start
        handle, _ = session.step(session.handle, (), "DISCH_TAC")
        handle, split = session.step(handle, (0,), "CONJ_TAC")
        branch = session.fork(handle)
        unchanged, failed = session.step(handle, (0, 0), "NO_TAC")
        right, left_pending = session.step(unchanged, (0, 1), "ASM_REWRITE_TAC []")
        _, right_pending = branch.step(branch.handle, (0, 0), "ASM_REWRITE_TAC []")
        completed, final_state = session.step(right, (0, 0), "ASM_REWRITE_TAC []")
        saved = session.checkpoint(completed)
        restored = HOLProofSession.from_checkpoint(task, project, saved, worker=worker)
        checks = {
            "fork_isolation": [goal.path for goal in left_pending.goals] == [(0, 0)]
            and [goal.path for goal in right_pending.goals] == [(0, 1)],
            "failed_tactic_keeps_state": unchanged == handle and failed.diagnostic is not None
            and failed.goals == split.goals,
            "checkpoint_replay": restored.inspect(restored.handle) == final_state
            and restored.candidate == session.candidate and not final_state.goals,
            "child_namespace_isolation": _isolation(worker, task, project, root),
        }
        with ThreadPoolExecutor(max_workers=1) as pool:
            independent = pool.submit(restored.finalize, restored.handle)
            stopped = _retirement(worker, task, project, root, cancel=Event())
            evidence = independent.result()
        checks["independent_verification"] = evidence.task_success is True
        checks["cancellation_reaps_descendants"] = stopped == {
            "outcome": "cancelled", "worker_retired": True, "descendants_reaped": True,
        }
    return {
        "environment_id": task.environment_id, "task_id": task.task_id, "prover_build": project.spec.prover_build,
        "startup_s": startup, "first_observation_s": first_observation_s, "checks": checks,
        "initial": initial.to_dict(), "split": split.to_dict(), "completed_candidate": restored.candidate,
        "verification": evidence.checker_outcome, "verified_artifact_id": evidence.artifact_id,
    }


def imports(prefix, root):
    project = _locked("warm-import", prefix, root / "cache")
    task = build_task(project)
    cold = HOLProofSession(task, project)
    with ThreadPoolExecutor(max_workers=2) as pool:
        cold_goal = pool.submit(cold.inspect, cold.handle)
        independent = pool.submit(verify, task, task.allowed_edits[0], prepared=project)
        with ForkedHOLLight(project) as worker:
            session = HOLProofSession(task, project, worker=worker)
            initial = session.inspect(session.handle)
            _, resolved = session.step(session.handle, (), "ACCEPT_TAC itpeval_identity")
            same = cold_goal.result() == initial
            evidence = independent.result()
            source = project.project / "helper.ml"
            source.chmod(0o600)
            source.write_text("(* deliberate drift in a disposable snapshot *)\n", encoding="utf-8")
            retired = False
            try:
                session.inspect(session.reset())
            except ValueError as error:
                retired = "retired after locked inputs changed" in str(error) and not worker.active
    return {
        "environment_id": task.environment_id, "task_id": task.task_id, "prover_build": project.spec.prover_build,
        "checks": {"cold_goal_parity": same, "locked_import_proof": not resolved.goals and evidence.task_success is True,
                   "drift_retires_worker": retired},
        "initial": initial.to_dict(), "checked_import_artifact": evidence.artifact_id,
    }


def deadline(prefix, root):
    project = _locked("interaction", prefix, root / "cache")
    task = build_task(project)
    task = replace(task, budgets=replace(task.budgets, timeout_s=2))
    with ForkedHOLLight(project) as worker:
        stopped = _retirement(worker, task, project, root)
    return {"checks": {"deadline_reaps_descendants": stopped == {
        "outcome": "timeout", "worker_retired": True, "descendants_reaped": True,
    }}, "observed": stopped}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    probes = {"branching": branching, "imports": imports, "deadline": deadline}
    with TemporaryDirectory(prefix="itpeval-hol-worker-check-") as temporary, ThreadPoolExecutor(max_workers=3) as pool:
        root = Path(temporary)
        pending = {}
        for name, probe in probes.items():
            workspace = root / name
            workspace.mkdir()
            pending[name] = pool.submit(probe, args.prefix, workspace)
        results = {name: future.result() for name, future in pending.items()}
    for name, result in results.items():
        print(name, result["checks"], flush=True)
    write_json(args.output, {"prover": "hol-light", "native_results": results})
    return 0 if all(all(result["checks"].values()) for result in results.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
