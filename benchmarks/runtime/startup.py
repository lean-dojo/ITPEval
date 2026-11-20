"""Measure fresh native startup with minimal input, independently of proof candidate work."""
import argparse
import json
import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.registry import curated_project, prover_ids
from itpeval.environments import prepare_project
from itpeval.runtime.process import run_process


def launch(prover, env, work):
    tools = env.prefix / prover / "bin"
    native_env = {key: os.environ[key] for key in ("HOME", "PATH", "LANG", "LC_ALL", "USER") if key in os.environ}
    native_env.update(env.environment)
    sentinel = "ITPEVAL_STARTUP_READY"
    stdin = None
    if prover == "lean4":
        command = [tools/"lean", "Startup.lean"]
        (work/"Startup.lean").write_text('#eval IO.println "' + sentinel + '"\n')
    elif prover == "rocq":
        command = [tools/"rocq", "compile", "Startup.v"]
        (work/"Startup.v").write_text('Goal True. idtac "' + sentinel + '". exact I. Qed.\n')
    elif prover == "acl2":
        command = [tools/"acl2"]
        stdin = work/"input"
        stdin.write_text('(cw "' + sentinel + '~%")\n:q\n')
    elif prover == "pvs":
        native_env.update(PVSMINUSQ="t", PVS_LOG_DIR=str(work/"logs"))
        command = [tools/"pvs", "-raw", "-E", '(progn (format t "~%' + sentinel + '~%") (bye))']
    elif prover == "hol-light":
        driver = work/"startup.ml"
        driver.write_text('print_endline "' + sentinel + '";;\n')
        command = [tools/"hollight-run", driver]
    elif prover == "hol4":
        driver = work/"startup.sml"
        driver.write_text('val _ = print "' + sentinel + '\\n";\n')
        command = [tools/"hol", "run", driver]
    elif prover == "isabelle":
        native_env["USER_HOME"] = str(work/"home")
        Path(native_env["USER_HOME"]).mkdir()
        command = [tools/"isabelle", "process", "-l", "HOL", "-e", 'writeln "' + sentinel + '"']
    elif prover == "agda":
        (work/"Startup.agda").write_text('module Startup where\n')
        command = [tools/"agda", "--safe", "--no-default-libraries", "--no-libraries", "--no-write-interfaces",
                   "-i", str(work), "Startup.agda"]
        sentinel = "Checking Startup"
    elif prover == "mizar":
        (work/"startup.miz").write_text("environ\n\nbegin\n")
        command = [tools/"mizf", "startup.miz"]
        sentinel = "Verifier based on"
    elif prover == "metamath":
        (work/"empty.mm").write_text('$c wff $.\n')
        command = [tools/"metamath", 'read empty.mm', 'exit']
        sentinel = "No errors were found."
    result = run_process(list(map(str, command)), cwd=work, env=native_env, timeout_s=300,
                         stdin_path=stdin, max_log_bytes=16384)
    if result.outcome != "exited" or result.returncode or sentinel not in result.stdout+result.stderr:
        raise ValueError(f"{prover}: {result.outcome}, rc={result.returncode}\n" +
                         (result.stdout + result.stderr)[-1400:])
    return {"native_ms": result.duration_ms, "peak_process_rss_bytes": result.peak_process_rss_bytes,
            "cpu_seconds": result.cpu_time_s, "execution": result.outcome, "returncode": result.returncode,
            "receipt": sentinel, "native_output_tail": (result.stdout + result.stderr)[-1400:]}


def sample(prover, prefix, cache, output):
    env = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    samples = []
    for mode in ("first_fresh_process", "repeat_fresh_process"):
        with TemporaryDirectory() as tmp:
            samples.append({"protocol": mode, **launch(prover, env, Path(tmp))})
    output.mkdir(parents=True, exist_ok=True)
    (output/(prover+".json")).write_text(json.dumps({"prover": prover, "environment_id": env.environment_id,
        "prover_build": env.spec.prover_build, "samples": samples}, indent=2)+"\n")


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    for key in ("prefix", "cache", "output"):
        cli.add_argument("--"+key, type=Path, required=True)
    cli.add_argument("--prover", action="append", choices=prover_ids())
    cli.add_argument("--workers", type=int, default=1)
    args = cli.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(sample, p, args.prefix, args.cache, args.output) for p in args.prover or prover_ids()]
        failed = []
        for job in futures:
            try:
                job.result()
            except ValueError as exc:
                failed.append(str(exc))
        if failed:
            raise SystemExit("\n".join(failed))
