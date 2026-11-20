from __future__ import annotations

import subprocess
import sys
import time
import json
import hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from eval.pipeline.config import PROVER_TIMEOUTS
from eval.pipeline.jsonl import load_checkpoint, repair_tail, result_writer, write_jsonl_atomic
from eval.pipeline.manifests import legacy_environments, records_digest
from eval.pipeline.task_profile import TaskProfile
from itpeval.core.records import digest
from itpeval.core.types import VerificationEvidence
from itpeval.learning.manifests import RunManifest
from eval.pipeline.records import translation_record_key, translation_record_label
from eval.pipeline.translation.scaffold import (
    ScaffoldError,
    extract_statement_response,
    validate_statement_output,
    validate_ungrounded_proof_output,
)

try:
    from itpeval.itp import run_itp, RunResult
except ModuleNotFoundError:
    repo_root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo_root))
    from itpeval.itp import run_itp, RunResult


@dataclass
class VerifyResult:
    ok: bool
    error: str
    duration_ms: int
    execution: str = "exited"
    returncode: int | None = None
    stdout: str = ""
    stderr: str = ""


def timeout_for(prover: str, *, hol_light_timeout_s: int | None = None) -> int:
    if prover == "hol-light" and hol_light_timeout_s is not None:
        return hol_light_timeout_s
    return PROVER_TIMEOUTS.get(prover, 120)


def verify(
    prover: str,
    code: str,
    timeout_s: int | None = None,
) -> VerifyResult:
    """Run the generated proof through the target ITP. Returns VerifyResult."""
    if timeout_s is None:
        timeout_s = timeout_for(prover)
    t0 = time.monotonic()
    try:
        # Raw mode sends the generated file directly to the selected prover adapter
        result: RunResult = run_itp(
            prover=prover,
            code=code,
            mode="raw",
            timeout_s=timeout_s,
        )
        error = ""
        if not result.ok:
            error = (result.stderr or result.stdout or "").strip()
        return VerifyResult(ok=result.ok, error=error, duration_ms=result.duration_ms,
                            returncode=getattr(result, "returncode", None), stdout=result.stdout, stderr=result.stderr)
    except subprocess.TimeoutExpired as exc:
        duration_ms = int((time.monotonic() - t0) * 1000)
        output = [data.decode("utf-8", errors="replace") if isinstance(data, bytes) else data or ""
                  for data in (exc.output, exc.stderr)]
        return VerifyResult(False, f"timeout after {timeout_s}s", duration_ms, "timeout", None, *output)
    except (OSError, RuntimeError) as exc:
        return VerifyResult(False, str(exc), int((time.monotonic() - t0) * 1000), execution="backend_error")


def verify_translation_record(
    record: dict,
    *,
    profile: TaskProfile | None = None,
    hol_light_timeout_s: int | None = None,
) -> dict:
    if profile is not None:
        return profile.verify(record)
    if record.get("task_id") or record.get("result_schema") == "itpeval-task-v1":
        raise ValueError("task-bound records require a trusted task profile")
    generated = record.get("generated", "") or ""

    def evidence(execution, outcome, duration=0, returncode=None, stdout="", stderr=""):
        if record.get("result_schema") != "itpeval-translation-v2":
            return {}
        status = "unchecked"
        if outcome == "accepted":
            status = "statement_accepted" if record.get("mode") == "stmts" else "artifact_accepted"
        return {"task_success": None, "evidence": {"schema_version": 1, "operation": "legacy_translation",
                "execution_outcome": execution, "checker_outcome": outcome, "completion_status": status,
                "target_preservation": "unbound", "duration_ms": duration, "returncode": returncode,
                "stdout": stdout, "stderr": stderr, "submitted_sha256": hashlib.sha256(generated.encode()).hexdigest()}}

    tgt_prover = record.get("tgt_prover", "")
    if not generated and record.get("translate_error") and record.get("result_schema") == "itpeval-translation-v2":
        return {**record, **evidence("generation_error", "not_run"), "verified": False,
                "verify_error": record["translate_error"], "verify_ms": 0}
    if generated and record.get("mode") == "stmts":
        raw_generated = generated
        try:
            generated = extract_statement_response(
                tgt_prover,
                raw_generated,
            )
            validate_statement_output(tgt_prover, generated)
        except ScaffoldError as exc:
            return {
                **record,
                "verified": False,
                **evidence("not_run", "policy_rejected"),
                "verify_error": str(exc),
                "verify_ms": 0,
            }
        if generated != raw_generated:
            record = {
                **record,
                "generated": generated,
                "raw_generated": record.get(
                    "raw_generated",
                    raw_generated,
                ),
            }
    if generated and record.get("mode") == "proofs":
        try:
            validate_ungrounded_proof_output(
                generated,
                prover=tgt_prover,
            )
        except ScaffoldError as exc:
            return {
                **record,
                "verified": False,
                **evidence("not_run", "policy_rejected"),
                "verify_error": str(exc),
                "verify_ms": 0,
                "admission_free": False,
            }
    # Empty model outputs are recorded as verification failures without invoking a prover
    if generated and tgt_prover:
        vr = verify(
            tgt_prover,
            generated,
            timeout_s=timeout_for(tgt_prover, hol_light_timeout_s=hol_light_timeout_s),
        )
        checked = {
            **record,
            **evidence(vr.execution, "accepted" if vr.ok else "unsuccessful", vr.duration_ms, vr.returncode,
                       vr.stdout, vr.stderr),
            "verified": vr.ok,
            "verify_error": vr.error,
            "verify_ms": vr.duration_ms,
        }
        if record.get("mode") == "proofs":
            checked["admission_free"] = True
        return checked
    return {**record, **evidence("not_run", "no_output"), "verified": False, "verify_error": "no output", "verify_ms": 0}


def failed_verification(record: dict, error: Exception, profile: TaskProfile | None = None) -> dict:
    message = f"verify error: {error}"
    row = {**record, "verified": False, "verify_error": message, "verify_ms": 0}
    if profile:
        failed = VerificationEvidence(profile.task.task_id, profile.task.environment_id, profile.task.artifact.artifact_id,
                                      "backend_error", "not_run", None, "unchecked", "unknown", stderr=message)
        row.update(task_success=None, environment_id=profile.task.environment_id, evidence=failed.to_dict())
    elif row.get("result_schema") == "itpeval-translation-v2":
        row.update(task_success=None, evidence={"schema_version": 1, "operation": "legacy_translation",
            "execution_outcome": "backend_error", "checker_outcome": "not_run", "completion_status": "unchecked",
            "target_preservation": "unbound", "duration_ms": 0, "returncode": None, "stdout": "", "stderr": message,
            "submitted_sha256": hashlib.sha256((row.get("generated") or "").encode()).hexdigest()})
    return row


def verify_translation_records(
    records: list[dict],
    out_path: Path,
    *,
    workers: int,
    profile: TaskProfile | None = None,
    hol_light_timeout_s: int | None = None,
) -> Path:
    total = len(records)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_path.with_suffix(out_path.suffix + ".ckpt.jsonl")

    if workers < 1:
        raise ValueError("workers must be positive")
    if profile is not None:
        profile.validate()
        if any(r.get("task_id") != profile.task.task_id or r.get("tgt_prover") != profile.task.prover for r in records):
            raise ValueError("input specifies another task or prover")
    elif any(r.get("task_id") or r.get("result_schema") == "itpeval-task-v1" for r in records):
        raise ValueError("task-bound records require a trusted task profile")
    dataset_id = records_digest(records)
    if profile:
        manifest = profile.manifest(dataset_id, {"source": "generated_records"})
    else:
        environments = legacy_environments(r["tgt_prover"] for r in records if r.get("tgt_prover"))
        manifest = RunManifest((), environments, "legacy_translation.verification.v1", dataset_id,
                               "prerecorded", {}, None, {"timeouts": PROVER_TIMEOUTS,
                                                         "hol_light_timeout_s": hol_light_timeout_s})
    with result_writer(out_path):
        manifest.bind(out_path, ckpt_path)
        repair_tail(ckpt_path)

        def key(record):
            # Historical proof IDs omit model identity and occur once per provider in batch output.
            return digest([translation_record_key(record), record.get("model"), record.get("model_id")])

        keys = [key(r) for r in records]
        if len(set(keys)) != len(keys):
            raise ValueError("duplicate attempts in verification input")
        done_map = load_checkpoint(ckpt_path, key)
        if any(r.get("verification_run_id") != manifest.run_id for r in done_map.values()):
            raise ValueError("checkpoint records differ from verification run manifest")
        if done_map:
            print(f"  Resuming from checkpoint: {ckpt_path} ({len(done_map)}/{total} done)", flush=True)

        # Checkpoints are append-only; the final output is rewritten in input order below
        remaining = [r for r in records if key(r) not in done_map]
        if not remaining:
            print("  Nothing to do: all entries already in checkpoint.", flush=True)
        else:
            print(f"  Verifying: {len(remaining)} remaining (workers={workers})", flush=True)

        done_count = len(done_map)
        with ckpt_path.open("a", encoding="utf-8") as ckpt, ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {
                pool.submit(
                    verify_translation_record,
                    r,
                    hol_light_timeout_s=hol_light_timeout_s,
                    profile=profile,
                ): r
                for r in remaining
            }
            for fut in as_completed(futures):
                source_record = futures[fut]
                try:
                    result = fut.result()
                except Exception as e:
                    result = failed_verification(source_record, e, profile)
                result["verification_run_id"] = manifest.run_id
                done_map[key(source_record)] = result
                ckpt.write(json.dumps(result, ensure_ascii=False) + "\n")
                ckpt.flush()
                done_count += 1
                status = "PASS" if result.get("verified") else "FAIL"
                print(f"  [{done_count}/{total}] {status}  {translation_record_label(result)}", flush=True)

        write_jsonl_atomic(
            out_path,
            (
                done_map.get(
                    key(r),
                    {**r, "verified": False, "verify_error": "missing", "verify_ms": 0},
                )
                for r in records
            ),
        )
        return out_path
