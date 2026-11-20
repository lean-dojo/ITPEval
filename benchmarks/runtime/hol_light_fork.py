"""Exercise a preinitialized HOL Light batch in forked, disposable OCaml children."""
import argparse
import json
from pathlib import Path
import re
import tempfile
from time import monotonic

from itpeval.backends.registry import curated_project, curated_task
from itpeval.environments import prepare_project
from itpeval.runtime.process import run_process
from itpeval.verification.policies import assemble


def experiment(prefix, cache):
    prepared = prepare_project("hol-light", curated_project("hol-light"), prefix=prefix, cache=cache)
    task = curated_task("hol-light", prepared.environment_id)
    with tempfile.TemporaryDirectory(prefix="itpeval-fork-") as tmp:
        root = Path(tmp)
        # The first child creates an OCaml binding. The next child must fail
        # if it tries to use that same binding without declaring it.
        sources = ['let itpeval_private_binding = TRUTH;;',
                   'let itpeval_foreign_binding = itpeval_private_binding;;']
        for edit in task.allowed_edits:
            sources.append(assemble(task, edit).files[0].data.decode())
        paths = []
        for index, source in enumerate(sources):
            path = root / f"candidate{index}.ml"
            path.write_text(source)
            paths.append(json.dumps(str(path)))
        driver = root / "fork_batch.ml"
        driver.write_text(
            'let run_one (i, path) =\n'
            '  flush_all ();\n'
            '  let started = Unix.gettimeofday () in\n'
            '  match Unix.fork () with\n'
            '  | 0 ->\n'
            '      let ok = try Toploop.use_file Format.std_formatter path with _ -> false in\n'
            '      flush_all (); exit (if ok then 0 else 1)\n'
            '  | pid ->\n'
            '      let (_, status) = Unix.waitpid [] pid in\n'
            '      let ok = (status = Unix.WEXITED 0) in\n'
            '      Printf.printf "ITPEVAL_FORK %d %b %.6f\\n%!" i ok (Unix.gettimeofday () -. started);;\n'
            'List.iter run_one [' + '; '.join(f'({i}, {p})' for i, p in enumerate(paths)) + '];;\n')
        # Compile the coordinator with standard OCaml syntax. Candidate files are
        # subsequently read by the initialized HOL Light toplevel parser.
        ocamlc = prefix.resolve() / "hol-light/opamroot/hol-light/bin/ocamlc"
        compilation = run_process([str(ocamlc), "-I", "+unix", "-I", "+compiler-libs",
                                   "-c", str(driver)], cwd=root, timeout_s=30)
        if compilation.returncode:
            raise RuntimeError(compilation.stderr)
        loader = root / "load.ml"
        loader.write_text('#directory "+unix";;\n#load "unix.cma";;\n#load '
                          + json.dumps(str(driver.with_suffix(".cmo"))) + ';;\n')
        started = monotonic()
        result = run_process([str(prefix.resolve() / 'hol-light/bin/hollight-run'), str(loader)],
                             timeout_s=360, cwd=root)
        elapsed = monotonic() - started
        outcomes = [(int(i), value == "true", float(sec)) for i, value, sec in
                    re.findall(r"ITPEVAL_FORK (\d+) (true|false) ([\d.]+)", result.stdout)]
        if result.returncode or [v for _, v, _ in outcomes] != [True, False, True, False, True]:
            raise RuntimeError("unexpected native fork results: " + result.stdout[-2800:] + result.stderr[-600:])
        return {"environment_id": prepared.environment_id, "task_id": task.task_id,
                "linux": True, "native_build": prepared.spec.prover_build,
                "wall_s": elapsed, "startup_and_shutdown_s": elapsed - sum(sec for _, _, sec in outcomes),
                "peak_process_rss_bytes": result.peak_process_rss_bytes, "results": outcomes}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(json.dumps(experiment(args.prefix, args.cache), indent=2) + "\n")
