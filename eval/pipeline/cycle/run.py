from __future__ import annotations

import argparse
import json
import hashlib
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from eval.pipeline.config import DATA_DIR, RESULTS_DIR
from eval.pipeline.jsonl import load_jsonl, repair_tail, result_writer
from eval.pipeline.manifests import records_digest
from itpeval.learning.manifests import RunManifest
from eval.pipeline.models import select_models
from eval.pipeline.translate import translate

CYCLE_DIR = RESULTS_DIR / "cycle"
DATA_FILE = DATA_DIR / "minif2f_nl4itp.jsonl"

_ITP_HEADERS = {
    "lean4":     "=== Lean 4 ===",
    "isabelle":  "=== Isabelle ===",
    "rocq":      "=== Rocq ===",
    "hol_light": "=== HOL Light ===",
}
_ITP_ORDER = ["lean4", "isabelle", "rocq", "hol_light"]


def _nl_to_lean4(nl: str) -> tuple[str, str]:
    system = (
        "You are an expert in interactive theorem proving, fluent in Lean 4. "
        "Your task is to translate mathematical theorem statements from natural language to Lean 4. "
        "Return only the complete Lean 4 statement file with the proof left as sorry, "
        "with no explanation or markdown fencing."
    )
    user = (
        "Translate the following natural language theorem statement into Lean 4. "
        "Do not prove the theorem — leave the proof body as sorry.\n\n"
        "=== Natural language statement ===\n"
        f"{nl.strip()}\n\n"
        "=== Lean 4 statement ==="
    )
    return system, user


def _lean4_to_nl(lean4: str) -> tuple[str, str]:
    system = (
        "You are an expert in interactive theorem proving, fluent in Lean 4 and mathematics. "
        "Your task is to explain formal theorem statements in natural language. "
        "Return only a concise natural language description of what the theorem claims, "
        "with no explanation of the formalization or markdown fencing."
    )
    user = (
        "Describe the following Lean 4 theorem statement in natural language. "
        "Give a concise mathematical statement of what the theorem claims.\n\n"
        "=== Lean 4 statement ===\n"
        f"{lean4.strip()}\n\n"
        "=== Natural language description ==="
    )
    return system, user


def _nl_to_4itps(nl: str) -> tuple[str, str]:
    system = (
        "You are an expert in interactive theorem proving, fluent in Lean 4, Isabelle/HOL, "
        "Rocq (Coq), and HOL Light. "
        "Your task is to translate mathematical theorem statements from natural language into "
        "formal statements in all four ITPs. "
        "Return only the statements in each prover using the exact section headers below, "
        "with proofs left as sorry or the equivalent placeholder. "
        "No explanation, no markdown fencing."
    )
    user = (
        "Translate the following natural language theorem statement into formal statements in all four ITPs. "
        "Leave proof bodies as sorry or the equivalent placeholder in each system.\n\n"
        "=== Natural language statement ===\n"
        f"{nl.strip()}\n\n"
        "=== Lean 4 ===\n\n"
        "=== Isabelle ===\n\n"
        "=== Rocq ===\n\n"
        "=== HOL Light ==="
    )
    return system, user


def _4itps_to_nl(itps: dict[str, str]) -> tuple[str, str]:
    system = (
        "You are an expert in interactive theorem proving, fluent in Lean 4, Isabelle/HOL, "
        "Rocq (Coq), and HOL Light. "
        "Your task is to explain formal theorem statements in natural language. "
        "Return only a concise natural language description of what the theorem claims, "
        "with no explanation or markdown fencing."
    )
    parts = [
        f"{_ITP_HEADERS[k]}\n{itps[k].strip()}"
        for k in _ITP_ORDER
        if itps.get(k)
    ]
    user = (
        "The following formal theorem statements all describe the same mathematical theorem. "
        "Give a concise natural language description of what the theorem claims.\n\n"
        + "\n\n".join(parts)
        + "\n\n=== Natural language description ==="
    )
    return system, user


def _parse_4itps(text: str) -> dict[str, str]:
    """Extract per-ITP sections from a model response containing section headers."""
    result = {k: "" for k in _ITP_ORDER}
    headers = [_ITP_HEADERS[k] for k in _ITP_ORDER]
    for i, key in enumerate(_ITP_ORDER):
        # Sections are parsed by exact headers produced in the cycle prompts
        start = text.find(headers[i])
        if start == -1:
            continue
        start += len(headers[i])
        end = len(text)
        for next_hdr in headers[i + 1:]:
            pos = text.find(next_hdr, start)
            if pos != -1:
                end = pos
                break
        result[key] = text[start:end].strip()
    return result


def _call(model_cfg: dict, system: str, user: str, max_tokens: int) -> tuple[str, str, int]:
    """Returns (output, error, elapsed_ms)."""
    t0 = time.monotonic()
    try:
        out = translate(system_prompt=system, user_prompt=user,
                        model_cfg=model_cfg, max_tokens=max_tokens)
        return out, "", int((time.monotonic() - t0) * 1000)
    except Exception as e:
        return "", str(e), int((time.monotonic() - t0) * 1000)


def _run_cycle1_record(record: dict, model_cfg: dict, max_tokens: int,
                       job_num: int, total: int) -> dict:
    name = record["name"]
    label = f"[{job_num}/{total}] cycle1 {name} model={model_cfg['label']}"
    print(label, flush=True)

    result: dict = {
        "name":        name,
        "split":       record["split"],
        "model":       model_cfg["label"],
        "nl_ref":      record["nl"],
        "lean4_ref":   record.get("lean4"),
        "step1_lean4": "", "step1_error": "", "step1_ms": 0,
        "step2_nl":    "", "step2_error": "", "step2_ms": 0,
        "step3_lean4": "", "step3_error": "", "step3_ms": 0,
    }

    out, err, ms = _call(model_cfg, *_nl_to_lean4(record["nl"]), max_tokens)
    result.update(step1_lean4=out, step1_error=err, step1_ms=ms)
    print(f"  step1 {'OK' if not err else 'FAIL'}  {label}", flush=True)
    if err:
        return result

    # Later cycle steps use generated text from earlier steps, not the references
    out, err, ms = _call(model_cfg, *_lean4_to_nl(result["step1_lean4"]), max_tokens)
    result.update(step2_nl=out, step2_error=err, step2_ms=ms)
    print(f"  step2 {'OK' if not err else 'FAIL'}  {label}", flush=True)
    if err:
        return result

    out, err, ms = _call(model_cfg, *_nl_to_lean4(result["step2_nl"]), max_tokens)
    result.update(step3_lean4=out, step3_error=err, step3_ms=ms)
    print(f"  step3 {'OK' if not err else 'FAIL'}  {label}", flush=True)

    return result


def _run_cycle2_record(record: dict, model_cfg: dict, max_tokens: int,
                       job_num: int, total: int) -> dict:
    name = record["name"]
    label = f"[{job_num}/{total}] cycle2 {name} model={model_cfg['label']}"
    print(label, flush=True)

    result: dict = {
        "name":     name,
        "split":    record["split"],
        "model":    model_cfg["label"],
        "nl_ref":       record["nl"],
        "lean4_ref":    record.get("lean4"),
        "isabelle_ref": record.get("isabelle"),
        "rocq_ref":     record.get("rocq"),
        "hol_light_ref": record.get("hol_light"),
        "step1_lean4": "",    "step1_isabelle": "",
        "step1_rocq": "",     "step1_hol_light": "",
        "step1_raw": "",      "step1_error": "", "step1_ms": 0,
        "step2_nl": "",       "step2_error": "", "step2_ms": 0,
        "step3_lean4": "",    "step3_isabelle": "",
        "step3_rocq": "",     "step3_hol_light": "",
        "step3_raw": "",      "step3_error": "", "step3_ms": 0,
    }

    out, err, ms = _call(model_cfg, *_nl_to_4itps(record["nl"]), max_tokens)
    result.update(step1_raw=out, step1_error=err, step1_ms=ms)
    if not err:
        parsed = _parse_4itps(out)
        for k, v in parsed.items():
            result[f"step1_{k}"] = v
    print(f"  step1 {'OK' if not err else 'FAIL'}  {label}", flush=True)
    if err:
        return result

    step1_itps = {k: result[f"step1_{k}"] for k in _ITP_ORDER}
    out, err, ms = _call(model_cfg, *_4itps_to_nl(step1_itps), max_tokens)
    result.update(step2_nl=out, step2_error=err, step2_ms=ms)
    print(f"  step2 {'OK' if not err else 'FAIL'}  {label}", flush=True)
    if err:
        return result

    out, err, ms = _call(model_cfg, *_nl_to_4itps(result["step2_nl"]), max_tokens)
    result.update(step3_raw=out, step3_error=err, step3_ms=ms)
    if not err:
        parsed3 = _parse_4itps(out)
        for k, v in parsed3.items():
            result[f"step3_{k}"] = v
    print(f"  step3 {'OK' if not err else 'FAIL'}  {label}", flush=True)

    return result


def run_cycle(
    *,
    cycle: int,
    models: list[dict],
    records: list[dict],
    workers: int,
    max_tokens: int,
    output_dir: Path | None = None,
) -> None:
    if cycle not in {1, 2} or min(workers, max_tokens) < 1:
        raise ValueError("cycle, worker and token budgets must be valid")
    if len({row["name"] for row in records}) != len(records):
        raise ValueError("duplicate theorem names in cycle input")
    sub_dir = (output_dir or CYCLE_DIR) / f"cycle{cycle}"
    runner = _run_cycle1_record if cycle == 1 else _run_cycle2_record
    dataset = records_digest(records)
    prompt = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    for model_cfg in models:
        out_path = sub_dir / f"{model_cfg['label']}.jsonl"
        manifest = RunManifest((), (), f"translation_cycle.{cycle}.v1", dataset, prompt,
                               model_cfg, None, {"max_tokens_per_call": max_tokens, "max_calls": 3})
        with result_writer(out_path):
            manifest.bind(out_path)
            repair_tail(out_path)
            previous = load_jsonl(out_path)
            if any(row.get("run_id") != manifest.run_id for row in previous):
                raise ValueError("saved cycle result differs from run manifest")
            done = {row["name"] for row in previous}
            remaining = [row for row in records if row["name"] not in done]
            print(f"cycle{cycle} {model_cfg['label']}: {len(remaining)} remaining, {len(done)} complete")
            with out_path.open("a", encoding="utf-8") as output, ThreadPoolExecutor(max_workers=workers) as pool:
                futures = {pool.submit(runner, row, model_cfg, max_tokens, i, len(remaining)): row
                           for i, row in enumerate(remaining, 1)}
                for future in as_completed(futures):
                    try:
                        result = future.result()
                    except Exception as error:
                        row = futures[future]
                        result = {"name": row["name"], "split": row["split"], "model": model_cfg["label"],
                                  "nl_ref": row["nl"], "step1_error": str(error), "execution_outcome": "generation_error"}
                    result["run_id"] = manifest.run_id
                    print(json.dumps(result, ensure_ascii=False), file=output, flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cycle",   choices=["1", "2", "both"], default="both",
                        help="Which cycle(s) to run (default: both)")
    parser.add_argument("--model",   help="Model label(s), comma-separated (default: all)")
    parser.add_argument("--workers", type=int, default=1,
                        help="Parallel workers per model (default: 1)")
    parser.add_argument("--max-tokens", type=int, default=4096,
                        help="Max output tokens per API call (default: 4096)")
    parser.add_argument("--output-dir", type=Path, help="new or resumable versioned result directory")
    parser.add_argument("--data",    default=str(DATA_FILE),
                        help=f"Input JSONL (default: {DATA_FILE})")
    parser.add_argument("--cycle100", action="store_true",
                        help="Only include the curated 100-record cycle subset")
    parser.add_argument("--split",   choices=["test", "valid", "both"], default="both",
                        help="Filter by MiniF2F split (default: both)")
    parser.add_argument("--all4",    action="store_true",
                        help="Only include records that have all 4 ITP statements")
    args = parser.parse_args()

    models = select_models(args.model)

    data_path = Path(args.data)
    if not data_path.exists():
        parser.exit(1, f"Data file not found: {data_path}\n"
                       "Regenerate eval data with: python3 data/build_eval_jsons.py\n")

    records = load_jsonl(data_path)
    if args.cycle100:
        records = [r for r in records if r.get("cycle100")]
    if args.split != "both":
        records = [r for r in records if r["split"] == args.split]
    if args.all4:
        records = [r for r in records
                   if all(r.get(k) for k in ["lean4", "isabelle", "rocq", "hol_light"])]
    print(f"Loaded {len(records)} records from {data_path}")

    cycles = [1, 2] if args.cycle == "both" else [int(args.cycle)]
    for c in cycles:
        run_cycle(
            cycle=c,
            models=models,
            records=records,
            workers=args.workers,
            max_tokens=args.max_tokens, output_dir=args.output_dir,
        )

    print("\nDone.")


if __name__ == "__main__":
    main()
