"""Run the SDK, sync, submit/collect, post-hoc and trainer entry points against a native checker."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from itpeval.backends.registry import curated_project, prover_ids
from itpeval.core.records import digest
from itpeval.core.types import VerificationEvidence
from itpeval.environments import prepare_project
from itpeval.learning.huggingface import VerifierReward
from itpeval.learning.qualification import _record
from itpeval.learning.rewards import proof_reward
from itpeval.verification.service import verify

from .completion import main as sync_main
from .task_profile import TaskProfile
from .translation.batch_jobs import save_job
from .translation.batch_run import main as batch_main
from .translation.verify_generated import main as posthoc_main

FIELDS = ("task_id", "environment_id", "artifact_id", "execution_outcome", "checker_outcome", "task_success",
          "target_preservation", "completion_status", "obligations", "evidence_references")
ROUTES = ("sdk", "sync", "batch", "posthoc", "trainer")


def _route(name, profile, candidate, directory):
    task, prepared = profile.task, profile.prepared
    lock = str(prepared.lock_path)
    source = directory / "candidate"
    raw, output = directory / "generated.jsonl", directory / (name + ".jsonl")
    details = {}
    if name == "sdk":
        evidence = verify(task, candidate, prepared=prepared)
    elif name == "trainer":
        attempts = []
        reward = VerifierReward({task.task_id: (task, prepared)}, record=attempts.append)
        received, = reward([[{"role": "assistant", "content": candidate}]], [task.task_id])
        row, = attempts
        if row["reward"] != received:
            raise ValueError("trainer callback and attempt record disagree")
        evidence = VerificationEvidence.from_dict(row.pop("evidence"))
        details = row
    else:
        if name == "sync":
            sync_main([lock, str(output), "--candidate", str(source)])
        elif name == "batch":
            job = directory / "job.json"
            batch_main(["submit", "--completion-lock", lock, "--candidate", str(source), "--job-file", str(job)])
            batch_main(["collect", str(job), "--completion-lock", lock, "--workers", "1", "--output", str(output)])
            plan = json.loads(job.read_bytes())
            details = {"generation_run_id": plan["run_id"], "transport": "prerecorded",
                       "batch_ids": plan["models"]["prerecorded"]["completed_batch_ids"],
                       "submitted": plan["requests"], "manifest": json.loads(job.with_suffix(".json.manifest.json").read_bytes())}
        elif name == "posthoc":
            sync_main([lock, str(raw), "--candidate", str(source), "--generate-only"])
            posthoc_main([str(raw), "--completion-lock", lock, "--workers", "1", "--output-dir", str(directory / "posthoc")])
            output = directory / "posthoc" / raw.name
            details["generated"] = json.loads(raw.read_bytes())
        else:
            raise ValueError(f"unknown route {name}")
        record = json.loads(output.read_bytes())
        details["verification_run_id"] = record.get("verification_run_id", record.get("run_id"))
        evidence = VerificationEvidence.from_dict(record["evidence"])
    return evidence, details


def qualify(prover, prefix, cache, output, report, *, workers=1):
    output.mkdir(parents=True, exist_ok=True)
    prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    profile = TaskProfile.from_lock(prepared.lock_path)
    task = profile.task
    summary = {}
    with tempfile.TemporaryDirectory() as tmp, ThreadPoolExecutor(max_workers=workers) as pool:
        jobs = {}
        for case, candidate in zip(("valid", "invalid"), task.allowed_edits[:2]):
            directory = Path(tmp) / case
            directory.mkdir()
            (directory / "candidate").write_bytes(candidate.encode("utf-8"))
            jobs[case] = {route: pool.submit(_route, route, profile, candidate, directory) for route in ROUTES}
        for case, pending in jobs.items():
            routed = {route: future.result() for route, future in pending.items()}
            native = {key: evidence.to_dict() for key, (evidence, _) in routed.items()}
            evidence = {key: {name: record[name] for name in FIELDS} for key, record in native.items()}
            rewards = {key: proof_reward(task, result).value for key, (result, _) in routed.items()}
            rewards["trainer"] = routed["trainer"][1]["reward"]
            summary[case] = {"evidence": evidence["sdk"], "native_evidence": native,
                             "routes": {name: data for name, (_, data) in routed.items()},
                             "evidence_hashes": {key: digest(value) for key, value in evidence.items()},
                             "rewards": rewards, "agrees": all(value == evidence["sdk"] for value in evidence.values())
                             and all(value == int(case == "valid") for value in rewards.values())}
    path = output / "evaluation.json"
    save_job(path, summary, indent=2)
    passed = all(row["agrees"] for row in summary.values())
    _record(report, [{"prover": prover, "prover_build": prepared.spec.prover_build,
                      "environment_id": prepared.environment_id, "operation": "evaluation_parity",
                      "status": "implemented/tested" if passed else "failed",
                      "evidence_path": os.path.relpath(path, report.parent)}])
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prover", required=True, choices=prover_ids())
    parser.add_argument("--workers", type=int, default=1, help="maximum simultaneous independent route checks")
    for key in ("prefix", "cache", "output", "report"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    raise SystemExit(0 if qualify(args.prover, args.prefix, args.cache, args.output / args.prover, args.report,
                                 workers=args.workers) else 1)


if __name__ == "__main__":
    main()
