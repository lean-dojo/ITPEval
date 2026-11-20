"""Compare HOLProofSession traces from fresh processes and disposable forked children."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import re
from tempfile import TemporaryDirectory
from time import perf_counter

from itpeval.backends.hol_tactics import HOLProofSession, HOLTactic
from itpeval.backends.projects import build_task
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.extraction.native_io import observations
from itpeval.runtime.process import run_process


_DRIVER = ('Sys.chdir (Sys.getenv "ITPEVAL_PROJECT");;\n'
           'load_path := Sys.getcwd () :: !load_path;;\n'
           'loadt (Sys.getenv "ITPEVAL_ENTRY");;\n')


def _fork_batch(root, prefix, entrypoint, jobs):
    """Compile the same static OCaml fork pattern used by hol_light_fork.py."""
    source = root / "coordinator.ml"
    arguments = "; ".join("(" + ", ".join(json.dumps(str(value)) for value in job) + ")" for job in jobs)
    source.write_text(
        'let run_one (name, source, trace, driver) =\n'
        '  flush_all ();\n'
        '  let start = Unix.gettimeofday () in\n'
        '  match Unix.fork () with\n'
        '  | 0 ->\n'
        '      Unix.putenv "ITPEVAL_PROJECT" source;\n'
        '      Unix.putenv "ITPEVAL_TRACE" trace;\n'
        '      Unix.putenv "ITPEVAL_ENTRY" ' + json.dumps(entrypoint) + ';\n'
        '      let ok = try Toploop.use_file Format.std_formatter driver with _ -> false in\n'
        '      flush_all (); exit (if ok then 0 else 1)\n'
        '  | pid ->\n'
        '      let (_, status) = Unix.waitpid [] pid in\n'
        '      let ok = (status = Unix.WEXITED 0) in\n'
        '      Printf.printf "ITPEVAL_AB %s %b %.6f\\n%!" name ok (Unix.gettimeofday () -. start);;\n'
        'List.iter run_one [' + arguments + '];;\n', encoding="utf-8")
    compiler = prefix / "hol-light/opamroot/hol-light/bin/ocamlc"
    result = run_process([str(compiler), "-I", "+unix", "-I", "+compiler-libs", "-c", str(source)],
                         cwd=root, timeout_s=30)
    if result.outcome != "exited" or result.returncode:
        raise RuntimeError("fork coordinator compilation failed: " + result.stderr)
    loader = root / "loader.ml"
    loader.write_text('#directory "+unix";;\n#load "unix.cma";;\n#load '
                      + json.dumps(str(source.with_suffix(".cmo"))) + ";;\n", encoding="utf-8")
    return loader


def experiment(prefix, cache):
    fixture = ROOT / "tests/fixtures/projects/hol-light/interaction"
    prepared = prepare_project("hol-light", fixture, prefix=prefix, cache=cache)
    task = build_task(prepared)
    session = HOLProofSession(task, prepared)
    template_bytes = (ROOT / "backends/hol_light/tactics.ml").read_bytes()
    template = template_bytes.decode("utf-8")
    slot = task.editable_regions[0]
    split = {(): HOLTactic((), "DISCH_TAC", 1), (0,): HOLTactic((0,), "CONJ_TAC", 2)}
    left = HOLTactic((0, 0), "ASM_REWRITE_TAC []", 0)
    right = HOLTactic((0, 1), "ASM_REWRITE_TAC []", 0)
    cases = {
        "initial": ({}, None),
        "split": (split, None),
        "left": (split, (left.path, left.text)),
        "right": (split, (right.path, right.text)),
        "wrong": (split, (left.path, "NO_TAC")),
        "left-again": (split, (left.path, left.text)),
        "closed": ({**split, left.path: left, right.path: right}, None),
    }
    native = prepared.prefix / "hol-light/bin/hollight-run"
    env = {key: os.environ[key] for key in ("HOME", "PATH", "USER", "LANG") if key in os.environ}
    env.update(prepared.environment)
    with TemporaryDirectory(prefix="itpeval-hol-warm-") as directory:
        root = Path(directory)

        def stage(name, case):
            work = root / name
            source = work / "project"
            task.artifact.materialize(source)
            artifact = source / slot.path
            artifact_data = artifact.read_bytes()
            actions, attempt = case
            tactic = session._render(actions, observe=[], attempt=attempt)
            instrumented = "(" + template.replace("ITPEVAL_TACTICS", tactic) + ")"
            artifact.write_bytes(artifact_data[:slot.start] + instrumented.encode() + artifact_data[slot.end:])
            driver = work / "run.ml"
            driver.write_text(_DRIVER, encoding="utf-8")
            return name, source, work / "trace", driver

        canaries = {
            "define-canary": ('let itpeval_warm_child_binding = TRUTH;;\n'
                              'Unix.putenv "ITPEVAL_WARM_CHILD_ENV" "private";;\n'
                              'load_path := [];;\n'),
            "reject-canary": "let itpeval_warm_must_be_missing = itpeval_warm_child_binding;;\n",
            "environment-canary": ('let () = assert (Sys.getenv_opt "ITPEVAL_WARM_CHILD_ENV" = None'
                                   ' && !load_path <> []);;\n'),
        }
        canary_jobs = []
        for name, source in canaries.items():
            driver = root / (name + ".ml")
            driver.write_text(source, encoding="utf-8")
            canary_jobs.append((name, root, root / (name + ".unused"), driver))

        warm = [stage(name, case) for name, case in cases.items()]
        cold = {name: stage("cold-" + name, cases[name]) for name in ("left", "wrong")}
        batch = [*canary_jobs, *warm]
        loader = _fork_batch(root, prepared.prefix, task.artifact.entrypoint, batch)

        def measure(driver, cwd, environment):
            prepared.validate()
            start = perf_counter()
            process = run_process([str(native), str(driver)], cwd=cwd, env=environment,
                                  timeout_s=task.budgets.timeout_s, max_log_bytes=task.budgets.max_log_bytes)
            return process, perf_counter() - start

        with ThreadPoolExecutor(max_workers=3) as pool:
            preloaded = pool.submit(measure, loader, root, env)
            fresh = {name: pool.submit(measure, driver, source,
                                      {**env, "ITPEVAL_PROJECT": str(source), "ITPEVAL_TRACE": str(trace),
                                       "ITPEVAL_ENTRY": task.artifact.entrypoint})
                     for name, (_, source, trace, driver) in cold.items()}
            parent, elapsed = preloaded.result()
            cold_runs = {name: operation.result() for name, operation in fresh.items()}
        timings = [{"case": name, "driver_succeeded": status == "true", "wall_s": float(wall_s)}
                   for name, status, wall_s in re.findall(r"ITPEVAL_AB ([\w-]+) (true|false) ([\d.]+)", parent.stdout)]
        if parent.outcome != "exited" or parent.returncode or [row["case"] for row in timings] != [job[0] for job in batch]:
            raise RuntimeError("preloaded batch did not report all children: " + parent.stdout[-2000:])
        if [row["driver_succeeded"] for row in timings[:3]] != [True, False, True]:
            raise RuntimeError("child isolation canaries did not pass")
        trace_paths = {name: trace for name, _, trace, _ in warm}
        for path in (*trace_paths.values(), *(case[2] for case in cold.values())):
            if path.stat().st_size > task.budgets.max_log_bytes:
                raise ValueError("native trace exceeds the task's output budget")
        byte_matches = {name: case[2].read_bytes() == trace_paths[name].read_bytes() for name, case in cold.items()}
        byte_matches["repeat_after_failure"] = trace_paths["left"].read_bytes() == trace_paths["left-again"].read_bytes()
        traces = {}
        for name, path in trace_paths.items():
            rows = observations(path)
            traces[name] = {"status": rows[-1][0], "open_goal_rows": sum(row[0] == "open" for row in rows)}
        expected = {"initial": 1, "split": 2, "left": 1, "right": 1, "wrong": 0, "left-again": 1, "closed": 0}
        if (not all(byte_matches.values()) or any(run.outcome != "exited" for run, _ in cold_runs.values())
                or any(trace != {"status": "raised" if name == "wrong" else "returned", "open_goal_rows": expected[name]}
                       for name, trace in traces.items())):
            raise RuntimeError("forked native observations differed from the expected proof states")
        return {
            "prover": task.prover, "environment_id": prepared.environment_id, "task_id": task.task_id,
            "prover_build": prepared.spec.prover_build, "version": prepared.build["version"],
            "trace_template_sha256": sha256(template_bytes).hexdigest(),
            "platform": prepared.build["platform"], "architecture": prepared.build["architecture"],
            "cold": {name: {"wall_s": wall_s, "returncode": process.returncode}
                     for name, (process, wall_s) in cold_runs.items()},
            "warm": {"wall_s": elapsed, "startup_and_shutdown_s": elapsed - sum(row["wall_s"] for row in timings),
                     "returncode": parent.returncode, "children": timings, "traces": traces},
            "identical_trace_bytes": byte_matches,
            "isolation": {"child_binding": True, "environment_variable": True, "load_path": True},
            "protocol": {
                "fixture": "itpeval/tests/fixtures/projects/hol-light/interaction",
                "run": "Two cold references and one static batch started together. The batch ran one child at a time.",
                "scope": "One conjunction fixture. The cold comparisons cover a successful leaf edit and a rejected tactic.",
                "timer": "Cold and batch wall time exclude staging and lock validation. Child time covers fork through wait.",
                "limits": "Each child loads the staged project over the stock HOL core. The supervisor applies a batch-level deadline.",
                "verification": "The pilot times native goal observations. Independent proof verification is recorded in evidence/hol-branches.json.",
                "trace": "A raised tactic emits no open-goal rows. The proof session keeps the previous state.",
                "reproduce": 'python -m benchmarks.runtime.hol_light_branch_fork --prefix "$ITPEVAL_PREFIX" --cache build/hol-fork-cache --output build/hol-light-branch-fork-pilot.json',
            },
            "remaining_checks": [
                "Revalidate the lock and coordinator identity before every request and retire a stale parent.",
                "Test imported project modules, cross-task namespace parity and private per-request output channels.",
                "Enforce each child deadline, cancellation, and resource budget and reap descendants on failure.",
            ],
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    write_json(args.output, experiment(args.prefix, args.cache))


if __name__ == "__main__":
    main()
