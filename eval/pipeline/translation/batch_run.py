from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone
from pathlib import Path

from eval.pipeline.batch import poll, submit
from eval.pipeline.config import BATCH_JOBS_DIR, VERIFIED_DIR
from eval.pipeline.models import select_models
from eval.pipeline.records import make_translation_record, translation_custom_id
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.prompt import build_prompt
from eval.pipeline.verify import verify_translation_records

POLL_INTERVAL_S = 60
GEMINI_CHUNK_SIZE = 200 
TERMINAL_STATUSES = {"failed", "expired", "cancelled"}


def _is_transient_poll_error(exc: Exception) -> bool:
    transient_types: list[type[BaseException]] = []
    try:
        import openai
        for name in ("APIConnectionError", "APITimeoutError", "RateLimitError"):
            cls = getattr(openai, name, None)
            if cls is not None:
                transient_types.append(cls)
    except ImportError:
        pass

    try:
        import httpx
        transient_types.extend([httpx.TimeoutException, httpx.TransportError])
    except ImportError:
        pass

    try:
        import requests
        transient_types.extend([requests.exceptions.Timeout, requests.exceptions.ConnectionError])
        if isinstance(exc, requests.exceptions.HTTPError):
            status = exc.response.status_code if exc.response is not None else None
            return status == 429 or (status is not None and status >= 500)
    except ImportError:
        pass

    return bool(transient_types) and isinstance(exc, tuple(transient_types))


def _make_request(pair: dict, mode: str) -> dict:
    system_prompt, user_prompt = build_prompt(
        title=pair["title"],
        src_prover=pair["src_prover"],
        tgt_prover=pair["tgt_prover"],
        source_content=pair["src_content"],
        mode=mode,
    )
    custom_id = translation_custom_id(pair)
    # Metadata fields are kept in the job file but omitted from provider requests
    return {
        "custom_id":     custom_id,
        "system_prompt": system_prompt,
        "user_prompt":   user_prompt,
        "_theorem_id":   pair["theorem_id"],
        "_title":        pair["title"],
        "_source":       pair["source"],
        "_tier":         pair["tier"],
        "_src_prover":   pair["src_prover"],
        "_tgt_prover":   pair["tgt_prover"],
        "_sample_idx":   0,
        "_temperature":  0.0,
        "_corpus":       pair.get("corpus"),
        "_source_sha256": pair.get("source_sha256"),
    }


def _chunk(lst: list, size: int) -> list[list]:
    return [lst[i:i + size] for i in range(0, len(lst), size)]


def _submit_with_retry(model_cfg: dict, requests: list[dict], max_retries: int = 5) -> str:
    """Submit with exponential backoff on 429 rate-limit errors and transient timeouts."""
    import requests as http_mod
    import httpx
    delay = 60
    for attempt in range(max_retries):
        try:
            return submit(model_cfg, requests)
        except http_mod.exceptions.HTTPError as e:
            if e.response is not None and e.response.status_code == 429 and attempt < max_retries - 1:
                print(f"  429 rate limit — retrying in {delay}s ...", flush=True)
                time.sleep(delay)
                delay *= 2
            else:
                raise
        except (httpx.WriteTimeout, httpx.ReadTimeout, httpx.ConnectTimeout) as e:
            if attempt < max_retries - 1:
                print(f"  network timeout ({e.__class__.__name__}) — retrying in {delay}s ...", flush=True)
                time.sleep(delay)
                delay *= 2
            else:
                raise


PROOFS_SOURCES = ["babel-formal", "hundred-theorems"]


def cmd_submit(args: argparse.Namespace) -> None:
    if args.sources:
        sources = args.sources.split(",")
    elif args.mode == "proofs":
        sources = PROOFS_SOURCES
    else:
        sources = None
    ids = [int(x) for x in args.ids.split(",")] if getattr(args, "ids", None) else None
    subset = None
    if getattr(args, "subset", None):
        subset_items = json.loads(Path(args.subset).read_text(encoding="utf-8"))
        subset = {(it["source"], int(it["theorem_id"])) for it in subset_items}
    models = select_models(args.models)
    pairs = load_pairs(args.mode, sources=sources, theorem_ids=ids, subset=subset)
    if getattr(args, "src", None):
        pairs = [p for p in pairs if p["src_prover"] == args.src]
    if getattr(args, "tgt", None):
        pairs = [p for p in pairs if p["tgt_prover"] == args.tgt]
    print(f"Loaded {len(pairs)} pairs (mode={args.mode})")

    if getattr(args, "dry_run", False):
        print(f"Dry run: {len(pairs)} pairs x {len(models)} models; no requests submitted")
        if pairs:
            request = _make_request(pairs[0], args.mode)
            print(request["system_prompt"])
            print(request["user_prompt"])
        return

    BATCH_JOBS_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    job_file = BATCH_JOBS_DIR / f"{timestamp}.json"

    job_data: dict = {
        "submitted_at": datetime.now(timezone.utc).isoformat(),
        "mode":         args.mode,
        "sources":      sources,
        "corpus":       "extended" if args.mode == "stmts" else "proofs",
        "models":       {},
        "requests":     [],
    }

    for model_cfg in models:
        label = model_cfg["label"]
        requests = [_make_request(p, args.mode) for p in pairs]

        api_requests = [
            {k: v for k, v in r.items() if not k.startswith("_")}
            for r in requests
        ]

        if not job_data["requests"]:
            job_data["requests"] = [
                {k: v for k, v in r.items() if k.startswith("_")}
                | {"custom_id": r["custom_id"]}
                for r in requests
            ]

        job_data["models"][label] = {
            "provider":  model_cfg["provider"],
            "model_id":  model_cfg["id"],
            "batch_ids": [],
            "status":    "submitted",
        }

        if model_cfg["provider"] == "gemini":
            # Gemini batches are chunked to keep each uploaded request file bounded
            chunks = _chunk(api_requests, GEMINI_CHUNK_SIZE)
            print(f"Submitting {len(api_requests)} requests for {label} "
                  f"in {len(chunks)} chunk(s) ...", flush=True)
            for i, chunk in enumerate(chunks):
                print(f"  chunk {i+1}/{len(chunks)} ({len(chunk)} requests) ...", flush=True)
                bid = _submit_with_retry(model_cfg, chunk)
                job_data["models"][label]["batch_ids"].append(bid)
                job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
                print(f"    {bid}")
        else:
            print(f"Submitting {len(api_requests)} requests for {label} ...", flush=True)
            bid = submit(model_cfg, api_requests)
            job_data["models"][label]["batch_ids"] = [bid]
            job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
            print(f"  {label}: {bid}")

    print(f"\nJob file: {job_file}")
    print(f"Run: python -m eval.pipeline.translation.batch_run collect {job_file}")


def cmd_collect(args: argparse.Namespace) -> None:
    job_file = Path(args.job_file)
    job_data = json.loads(job_file.read_text())

    meta = {r["custom_id"]: r for r in job_data["requests"]}
    for info in job_data["models"].values():
        if "batch_id" in info and "batch_ids" not in info:
            info["batch_ids"] = [info["batch_id"]] if info["batch_id"] else []

    pending: dict[str, list[str]] = {}
    collected: dict[str, dict[str, str]] = {} 
    terminal_errors: list[str] = []

    for label, info in job_data["models"].items():
        # Completed job files can be collected without provider API access
        if info["status"] in TERMINAL_STATUSES:
            terminal_errors.append(f"{label}: previous collect recorded status={info['status']}")
            collected[label] = info.get("results", {})
            continue
        if info["status"] == "completed":
            collected[label] = info.get("results", {})
            continue
        pending[label] = list(info["batch_ids"])
        collected[label] = {}

    if pending:
        print(f"Polling {list(pending)} ...")

    while pending:
        time.sleep(POLL_INTERVAL_S)
        still_pending: dict[str, list[str]] = {}

        for label, batch_ids in pending.items():
            info = job_data["models"][label]
            model_cfg = {
                "label": label,
                "id": info["model_id"],
                "provider": info["provider"],
            }
            remaining_ids = []

            for bid in batch_ids:
                try:
                    status, results = poll(model_cfg, bid)
                except Exception as e:
                    if _is_transient_poll_error(e):
                        print(f"  {label} [{bid[:20]}]: transient error ({e}), will retry")
                        remaining_ids.append(bid)
                    else:
                        msg = f"{label} [{bid}]: poll failed with non-transient error: {e}"
                        print(f"  {msg}", flush=True)
                        info["status"] = "failed"
                        info.setdefault("errors", []).append(msg)
                        terminal_errors.append(msg)
                        job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
                    continue

                print(f"  {label} [{bid[:20]}...]: {status}")

                if status == "completed" and results is not None:
                    collected[label].update(results)
                elif status in TERMINAL_STATUSES:
                    msg = f"{label} [{bid}]: batch {status}"
                    print(f"  {msg}", flush=True)
                    info["status"] = status
                    info.setdefault("failed_batch_ids", []).append(bid)
                    info.setdefault("errors", []).append(msg)
                    terminal_errors.append(msg)
                    job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
                else:
                    remaining_ids.append(bid)

            if remaining_ids:
                still_pending[label] = remaining_ids
            else:
                info["status"] = "completed"
                info["results"] = collected[label]
                job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))

        pending = still_pending

    if terminal_errors:
        raise SystemExit(
            "Batch collection stopped because one or more provider jobs failed:\n"
            + "\n".join(f"- {msg}" for msg in terminal_errors)
        )

    VERIFIED_DIR.mkdir(parents=True, exist_ok=True)
    mode = job_data["mode"]
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    results_path = VERIFIED_DIR / f"batch_{mode}_{timestamp}.jsonl"
    print(f"\nPreparing generated records for {results_path} ...")

    expected_ids = list(meta)
    records: list[dict] = []
    for label, results in collected.items():
        info = job_data["models"][label]
        model_cfg = {
            "label": label,
            "id": info["model_id"],
            "provider": info["provider"],
        }
        missing = sorted(set(expected_ids) - set(results))
        if missing:
            info["missing_output_count"] = len(missing)
            job_file.write_text(json.dumps(job_data, indent=2, ensure_ascii=False))
            print(f"  {label}: {len(missing)} requested outputs missing; writing no-output records")
        for custom_id in expected_ids:
            generated = results.get(custom_id, "")
            m = meta.get(custom_id, {})
            pair = {
                "theorem_id": m.get("_theorem_id"),
                "title": m.get("_title"),
                "source": m.get("_source"),
                "tier": m.get("_tier"),
                "src_prover": m.get("_src_prover"),
                "tgt_prover": m.get("_tgt_prover", ""),
                "corpus": m.get("_corpus"),
                "source_sha256": m.get("_source_sha256"),
            }
            records.append(make_translation_record(
                pair=pair,
                model_cfg=model_cfg,
                mode=mode,
                generated=generated,
                sample_idx=int(m.get("_sample_idx", 0)),
                temperature=float(m.get("_temperature", 0.0)),
                custom_id=custom_id,
            ))

    print(f"\nVerifying and writing {len(records)} records to {results_path} ...")
    # Batch outputs enter the same verifier path as generated JSONL files
    verify_translation_records(records, results_path, workers=args.workers)

    print(f"\nDone. Results: {results_path}")


def main() -> None:
    parser = argparse.ArgumentParser(prog="batch_run")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_submit = sub.add_parser("submit", help="Submit batch jobs")
    p_submit.add_argument("--mode",    choices=["stmts", "proofs"], default="stmts",
                          help="Translate statements or full proofs (default: stmts)")
    p_submit.add_argument("--sources", help="Comma-separated benchmark names (default: all)")
    p_submit.add_argument("--src", help="Filter to one source prover")
    p_submit.add_argument("--tgt", help="Filter to one target prover")
    p_submit.add_argument("--dry-run", action="store_true", help="Preview selection and first prompt without submitting")
    p_submit.add_argument("--ids",     help="Comma-separated theorem IDs to include (default: all)")
    p_submit.add_argument(
        "--subset",
        help="Path to a subset JSON file (list of {source,theorem_id}) to restrict evaluation",
    )
    p_submit.add_argument("--models",  help="Comma-separated model labels (default: all in config)")

    p_collect = sub.add_parser("collect", help="Poll, verify, and write results")
    p_collect.add_argument("job_file", help="Path to the .json job file from submit")
    p_collect.add_argument("--workers", type=int, default=8,
                           help="Parallel verification workers (default: 8)")

    args = parser.parse_args()
    if args.cmd == "submit":
        cmd_submit(args)
    else:
        cmd_collect(args)


if __name__ == "__main__":
    main()
