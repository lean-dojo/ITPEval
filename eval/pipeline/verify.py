from __future__ import annotations

import subprocess
import sys
import time
import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from eval.pipeline.config import PROVER_TIMEOUTS
from eval.pipeline.jsonl import load_checkpoint, write_jsonl_atomic
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
        return VerifyResult(ok=result.ok, error=error, duration_ms=result.duration_ms)
    except subprocess.TimeoutExpired:
        duration_ms = int((time.monotonic() - t0) * 1000)
        return VerifyResult(ok=False, error=f"timeout after {timeout_s}s", duration_ms=duration_ms)


def verify_translation_record(
    record: dict,
    *,
    hol_light_timeout_s: int | None = None,
) -> dict:
    generated = record.get("generated", "") or ""
    tgt_prover = record.get("tgt_prover", "")
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
            "verified": vr.ok,
            "verify_error": vr.error,
            "verify_ms": vr.duration_ms,
        }
        if record.get("mode") == "proofs":
            checked["admission_free"] = True
        return checked
    return {**record, "verified": False, "verify_error": "no output", "verify_ms": 0}


def verify_translation_records(
    records: list[dict],
    out_path: Path,
    *,
    workers: int,
    hol_light_timeout_s: int | None = None,
) -> Path:
    total = len(records)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_path.with_suffix(out_path.suffix + ".ckpt.jsonl")

    done_map = load_checkpoint(ckpt_path, translation_record_key)
    if done_map:
        print(f"  Resuming from checkpoint: {ckpt_path} ({len(done_map)}/{total} done)", flush=True)

    # Checkpoints are append-only; the final output is rewritten in input order below
    remaining = [r for r in records if translation_record_key(r) not in done_map]
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
            ): r
            for r in remaining
        }
        for fut in as_completed(futures):
            source_record = futures[fut]
            try:
                result = fut.result()
            except Exception as e:
                result = {
                    **source_record,
                    "verified": False,
                    "verify_error": f"verify error: {e}",
                    "verify_ms": 0,
                }
            key = translation_record_key(result)
            done_map[key] = result
            ckpt.write(json.dumps(result, ensure_ascii=False) + "\n")
            ckpt.flush()
            done_count += 1
            status = "PASS" if result.get("verified") else "FAIL"
            print(f"  [{done_count}/{total}] {status}  {translation_record_label(result)}", flush=True)

    write_jsonl_atomic(
        out_path,
        (
            done_map.get(
                translation_record_key(r),
                {**r, "verified": False, "verify_error": "missing", "verify_ms": 0},
            )
            for r in records
        ),
    )
    return out_path
