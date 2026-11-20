"""Run the native release qualification for each selected prover from an installed wheel."""
import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from itpeval.backends.registry import prover_ids
from itpeval.environments.cache import write_json


ROOT = Path(__file__).resolve().parents[1]


def qualify(prover, args):
    lockdir = args.output / ".locks"
    lockdir.mkdir(parents=True, exist_ok=True)
    with (lockdir / prover).open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        # Invalidate the prior installed-run receipt before retrying a shard.
        # Its replacement is published only after every native entry point exits.
        (args.output / "evidence" / prover / "smoke.json").unlink(missing_ok=True)
        _run(prover, args)


def _run(prover, args):
    output = args.output / "evidence"
    report = args.output / "qualification.jsonl"
    env = {**os.environ, "ITPEVAL_PREFIX": str(args.prefix)}
    env.pop("PYTHONPATH", None)
    common = ["--prefix", args.prefix, "--cache", args.cache, "--output", output, "--report", report]
    with tempfile.TemporaryDirectory() as scratch:
        def run(*arguments):
            print(f"[{prover}] " + " ".join(map(str, arguments)), flush=True)
            with tempfile.TemporaryDirectory(dir=scratch) as cwd:
                subprocess.run([args.python, "-I", *arguments], cwd=cwd, env=env, check=True)

        # A matrix runner installs precisely this wheel. Refuse to publish
        # checkout/editable evidence under an installed distribution's identity.
        verify_install = (
            "import importlib.metadata as m,json,sys;"
            "direct=json.loads(m.distribution('itpeval').read_text('direct_url.json'));"
            "assert direct['archive_info']['hashes']['sha256']==sys.argv[1], 'installed wheel digest differs'"
        )
        wheel, = args.distributions.glob("*.whl")
        wheel_hash = hashlib.sha256(wheel.read_bytes()).hexdigest()
        run("-c", verify_install, wheel_hash)

        commands = [("-m", module, "--prover", prover, *common) for module in
                    ("itpeval.learning.qualification", "eval.pipeline.qualification",
                     "itpeval.tests.conformance.extraction", "itpeval.tests.conformance.task_policy")]
        commands.append(("-m", "itpeval.cli", "--run-dir", output / prover / "smoke", "check",
                         "--task", "arith_2_plus_2", prover))
        commands.append((ROOT / "benchmarks/runtime/negative_cases.py", "--prover", prover, "--prefix", args.prefix,
                         "--cache", args.cache, "--output", output / prover / "malformed"))
        # Each producer owns a separate receipt and the JSONL publisher has a
        # cross-process lock. Workers share only the prepared input cache.
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.probe_jobs) as probes:
            futures = [probes.submit(run, *command) for command in commands]
            for future in concurrent.futures.as_completed(futures):
                future.result()
        if prover == "lean4":
            run("-m", "itpeval.tests.conformance.lean_tools", *common)
            run("-m", "itpeval.tests.conformance.equivalence", *common)
            run("-m", "itpeval.learning.goal_search", "--prefix", args.prefix, "--cache", args.cache,
                "--output", output / prover / "goal-search.jsonl")
        if prover == "rocq":
            corpus = Path(scratch) / "benchmark"
            env["ITPEVAL_DATA_DIR"] = str(corpus / "eval/data")
            env["ITPEVAL_RESULTS_DIR"] = str(Path(scratch) / "results")
            run("-m", "eval.datasets", "--destination", corpus, "--from-checkout", ROOT)
            run("-m", "eval.pipeline.published_qualification", "--output", output / prover / "published-translation.json")
        if prover == "metamath":
            run("-m", "itpeval.learning.premise_search", "--prefix", args.prefix, "--cache", args.cache,
                "--output", output / prover / "premise-search.jsonl")
            run("-m", "itpeval.learning.grpo_example", "--prefix", args.prefix, "--cache", args.cache,
                "--output", output / prover / "grpo")
        if prover == "isabelle":
            run(ROOT / "benchmarks/runtime/isa_repl.py", *common, "--integrations", args.isa_integrations)
        else:
            run(ROOT / "benchmarks/runtime/interaction.py", "--prover", prover, *common)
        smoke = json.loads((output / prover / "smoke/results.jsonl").read_text().splitlines()[-1])
        if smoke["prover"] != prover or smoke["status"] != "ok" or smoke["returncode"] != 0:
            raise ValueError(f"missing successful installed CLI smoke for {prover}")
        # Retain a portable receipt in addition to the full host-local logs.
        receipt = {k: smoke[k] for k in ("task", "prover", "status", "execution_outcome", "returncode",
                                         "duration_ms", "version")}
        receipt["log_sha256"] = hashlib.sha256(Path(smoke["log_path"]).read_bytes()).hexdigest()
        receipt["wheel_sha256"] = wheel_hash
        write_json(output / prover / "smoke.json", receipt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "output", "distributions"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--python", type=Path, default=Path(sys.executable), help="interpreter with this wheel installed")
    parser.add_argument("--prover", choices=prover_ids(), action="append")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--probe-jobs", type=int, default=1, help="maximum concurrent independent probes per prover")
    parser.add_argument("--isa-integrations", type=Path, help="directory containing isa_repl and auto_sledgehammer")
    args = parser.parse_args()
    if args.jobs <= 0 or args.probe_jobs <= 0:
        parser.error("worker limits must be positive")
    # Do not resolve a venv interpreter symlink back to the system interpreter.
    args.python = args.python.absolute()
    args.prefix, args.cache, args.output, args.distributions = (
        p.resolve() for p in (args.prefix, args.cache, args.output, args.distributions))
    args.isa_integrations = (args.isa_integrations or args.prefix / "auxiliary/isabelle").resolve()
    provers = list(dict.fromkeys(args.prover or ("hol-light", *(p for p in prover_ids() if p != "hol-light"))))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        results = {executor.submit(qualify, p, args): p for p in provers}
        failures = []
        for future in concurrent.futures.as_completed(results):
            try:
                future.result()
            except (OSError, KeyError, ValueError, subprocess.SubprocessError) as error:
                failures.append(results[future])
                print(f"[{results[future]}] {error}", file=sys.stderr, flush=True)
    if failures:
        raise SystemExit("Failed native qualifications: " + ", ".join(failures))


if __name__ == "__main__":
    main()
