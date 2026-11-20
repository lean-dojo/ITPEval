from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone
from pathlib import Path
from uuid import uuid4

from itpeval.core.records import digest
from eval.pipeline.jsonl import result_writer
from eval.pipeline.translation.batch_jobs import generation_manifest, poll_recording, save_job, submit_recording, validate_job

from eval.pipeline.batch import poll, submit
from eval.pipeline.config import BATCH_JOBS_DIR, VERIFIED_DIR
from eval.pipeline.models import select_models
from eval.pipeline.records import make_translation_record, translation_custom_id
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.prompt import build_prompt
from eval.pipeline.verify import verify_translation_records
from eval.pipeline.task_profile import TaskProfile, completion_record, completion_request

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


PROOFS_SOURCES = ["babel-formal", "hundred-theorems"]


def cmd_submit(args: argparse.Namespace) -> Path | None:
    lock = getattr(args, "completion_lock", None)
    if args.sources:
        sources = args.sources.split(",")
    elif args.mode == "proofs" and not lock:
        sources = PROOFS_SOURCES
    else:
        sources = None
    ids = [int(x) for x in args.ids.split(",")] if getattr(args, "ids", None) else None
    subset = None
    if getattr(args, "subset", None):
        subset_items = json.loads(Path(args.subset).read_text(encoding="utf-8"))
        subset = {(it["source"], int(it["theorem_id"])) for it in subset_items}
    profile = TaskProfile.from_lock(Path(lock), getattr(args, "task_manifest", "completion.json")) if lock else None
    corpus = getattr(args, "corpus", None)
    if profile and any((sources, ids, subset, corpus, getattr(args, "src", None), getattr(args, "tgt", None))):
        raise ValueError("benchmark filters cannot be applied to a fixed completion task")
    pairs = [] if profile else load_pairs(args.mode, sources=sources, theorem_ids=ids, subset=subset, corpus=corpus)
    if getattr(args, "src", None):
        pairs = [p for p in pairs if p["src_prover"] == args.src]
    if getattr(args, "tgt", None):
        pairs = [p for p in pairs if p["tgt_prover"] == args.tgt]
    requests = [completion_request(profile)] if profile else [_make_request(p, args.mode) for p in pairs]
    ids = {r["custom_id"] for r in requests}
    if len(ids) != len(requests):
        raise ValueError("duplicate batch request identities")
    transcript = getattr(args, "responses", None)
    candidate = getattr(args, "candidate", None)
    responses = None
    if transcript is not None or candidate is not None:
        if getattr(args, "models", None):
            raise ValueError("select either a provider model or prerecorded responses")
        if candidate is not None:
            if not profile or len(requests) != 1:
                raise ValueError("--candidate requires a single trusted completion task")
            responses = {requests[0]["custom_id"]: Path(candidate).read_bytes().decode("utf-8")}
        else:
            responses = json.loads(Path(transcript).read_bytes())
        if (not isinstance(responses, dict) or responses.keys() - ids or
                any(not isinstance(v, str) and v is not None for v in responses.values())):
            raise ValueError("prerecorded responses must map requested IDs to raw text or null")
        models = [{"id": digest(responses), "label": "prerecorded", "provider": "prerecorded"}]
    else:
        models = select_models(args.models)
    supported = {"prerecorded", "openai", "anthropic", "gemini"}
    if responses is None and not args.models:
        models = [model for model in models if model["provider"] in supported]
    if any(model["provider"] not in supported for model in models):
        raise ValueError("the selected provider has no batch transport")
    if len({model["label"] for model in models}) != len(models):
        raise ValueError("duplicate batch model labels")
    print(f"Prepared {len(requests)} requests per model")
    if getattr(args, "dry_run", False):
        print(f"Dry run: {len(requests)} requests x {len(models)} models; no requests submitted")
        if requests:
            request = requests[0]
            print(request["system_prompt"])
            print(request["user_prompt"])
        return

    job_file = getattr(args, "job_file", None)
    if job_file is None:
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        job_file = BATCH_JOBS_DIR / f"{timestamp}_{uuid4().hex[:10]}.json"
    job_file = Path(job_file)
    planned = {}
    for model in models:
        provider = model["provider"]
        planned[model["label"]] = {"provider": provider, "model_id": model["id"],
            "chunk_size": GEMINI_CHUNK_SIZE if provider == "gemini" else max(len(requests), 1),
            "max_tokens": 4096 if provider == "anthropic" else 16000, "temperature": None if provider == "openai" else 0.0,
            "batch_ids": [], "status": "submitting"}
    job_data = {"job_version": 1, "submitted_at": datetime.now(timezone.utc).isoformat(),
                "mode": "proof_completion" if profile else args.mode, "sources": sources,
                "corpus": None if profile else corpus or ("extended" if args.mode == "stmts" else "proofs"),
                "task_id": profile.task.task_id if profile else None,
                "environment_id": profile.task.environment_id if profile else None,
                "budgets": {"checker": profile.task.budgets.to_dict()} if profile else {},
                "models": planned, "requests": requests}
    manifest = generation_manifest(job_data)
    with result_writer(job_file):
        manifest.bind(job_file)
        if job_file.exists():
            job_data = json.loads(job_file.read_bytes())
            validate_job(job_file, job_data)
        else:
            job_data["run_id"] = manifest.run_id
            save_job(job_file, job_data)
        api_requests = [{k: v for k, v in r.items() if not k.startswith("_")} for r in requests]
        recovery = dict(value.split("=", 1) for value in getattr(args, "recover_batch", ()))
        retry = set(getattr(args, "retry_unconfirmed", ()))
        if recovery.keys() & retry:
            raise ValueError("an unconfirmed submission can be either recovered or retried")
        pending = {label for label, info in job_data["models"].items() if info.get("pending_chunk") is not None}
        if (recovery.keys() | retry) - pending or any(not value for value in recovery.values()):
            raise ValueError("submission recovery requires an unconfirmed model label and its provider batch ID")
        for label, info in job_data["models"].items():
            if info["status"] != "submitting":
                continue
            model = {"label": label, "provider": info["provider"], "id": info["model_id"]}
            chunks = _chunk(api_requests, info["chunk_size"])
            for index in range(len(info["batch_ids"]), len(chunks)):
                if info.get("pending_chunk") is not None and responses is None:
                    if label in recovery:
                        info["batch_ids"].append(recovery.pop(label))
                        del info["pending_chunk"]
                        save_job(job_file, job_data)
                        continue
                    if label not in retry:
                        raise ValueError(f"remote submission {label} chunk {index} is unconfirmed; "
                                         "resume using --recover-batch LABEL=ID or --retry-unconfirmed LABEL")
                    retry.remove(label)
                info["pending_chunk"] = index
                save_job(job_file, job_data)
                if responses is not None:
                    handle = submit_recording(job_file.with_suffix(job_file.suffix + ".spool"), chunks[index], responses)
                else:
                    handle = submit(model, chunks[index], max_tokens=info["max_tokens"], temperature=info["temperature"])
                info["batch_ids"].append(handle)
                del info["pending_chunk"]
                save_job(job_file, job_data)
            info["status"] = "submitted"
            save_job(job_file, job_data)
        if recovery or retry:
            raise ValueError(f"no unconfirmed submission for {', '.join(sorted(recovery.keys() | retry))}")
    print(f"Job file: {job_file}")
    return job_file


def cmd_collect(args: argparse.Namespace) -> None:
    job_file = Path(args.job_file)
    with result_writer(job_file):
        return _collect(args, job_file)


def _collect(args, job_file):
    job_data = json.loads(job_file.read_bytes())
    validate_job(job_file, job_data)
    lock = getattr(args, "completion_lock", None)
    profile = TaskProfile.from_lock(Path(lock), getattr(args, "task_manifest", "completion.json")) if lock else None
    if (job_data.get("task_id") != (profile.task.task_id if profile else None)
            or (profile and job_data.get("environment_id", profile.task.environment_id) != profile.task.environment_id)):
        raise ValueError("batch requires its original trusted completion lock")
    if any(info["status"] == "submitting" for info in job_data["models"].values()):
        raise ValueError("submission is incomplete; rerun submit with its original options and --job-file")
    meta = {r["custom_id"]: r for r in job_data["requests"]}
    for info in job_data["models"].values():
        if "batch_id" in info and "batch_ids" not in info:
            info["batch_ids"] = [info["batch_id"]] if info["batch_id"] else []

    pending: dict[str, list[str]] = {}
    collected = {}
    terminal_errors: list[str] = []

    for label, info in job_data["models"].items():
        collected[label] = dict(info.get("results", {}))
        if collected[label].keys() - meta.keys():
            raise ValueError("saved batch results contain unknown request identities")
        terminal_errors.extend(info.get("errors", ()))
        if info["status"] == "completed":
            continue
        finished = set(info.get("completed_batch_ids", ())) | set(info.get("failed_batch_ids", ()))
        if info["status"] in TERMINAL_STATUSES and not finished:
            terminal_errors.append(f"{label}: previous collect recorded status={info['status']}")
            continue
        pending_ids = [bid for bid in info["batch_ids"] if bid not in finished]
        if pending_ids:
            pending[label] = pending_ids

    if pending:
        print(f"Polling {list(pending)} ...")

    while pending:
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
                    if info["provider"] == "prerecorded":
                        status, results = poll_recording(job_file.with_suffix(job_file.suffix + ".spool"), bid)
                    else:
                        status, results = poll(model_cfg, bid)
                except Exception as e:
                    if info["provider"] == "prerecorded" or isinstance(e, ValueError):
                        raise
                    if _is_transient_poll_error(e):
                        print(f"  {label} [{bid[:20]}]: transient error ({e}), will retry")
                        remaining_ids.append(bid)
                    else:
                        msg = f"{label} [{bid}]: poll failed with non-transient error: {e}"
                        print(f"  {msg}", flush=True)
                        info.setdefault("failed_batch_ids", []).append(bid)
                        info.setdefault("errors", []).append(msg)
                        terminal_errors.append(msg)
                        save_job(job_file, job_data)
                    continue

                print(f"  {label} [{bid[:20]}...]: {status}")

                if results is not None and status in TERMINAL_STATUSES | {"completed"}:
                    chunk_size = info.get("chunk_size")
                    expected = set(meta)
                    if chunk_size:
                        index = info["batch_ids"].index(bid)
                        expected = set(list(meta)[index * chunk_size:(index + 1) * chunk_size])
                    if results.keys() - expected or results.keys() & collected[label].keys():
                        raise ValueError("batch results contain unexpected or repeated request identities")
                    collected[label].update(results)
                    info["results"] = collected[label]
                if status == "completed":
                    info.setdefault("completed_batch_ids", []).append(bid)
                    save_job(job_file, job_data)
                elif status in TERMINAL_STATUSES:
                    msg = f"{label} [{bid}]: batch {status}"
                    print(f"  {msg}", flush=True)
                    info.setdefault("failed_batch_ids", []).append(bid)
                    info.setdefault("errors", []).append(msg)
                    terminal_errors.append(msg)
                    save_job(job_file, job_data)
                else:
                    remaining_ids.append(bid)

            if remaining_ids:
                still_pending[label] = remaining_ids
            else:
                info["status"] = "failed" if info.get("failed_batch_ids") else "completed"
                info["results"] = collected[label]
                save_job(job_file, job_data)

        pending = still_pending
        if pending:
            time.sleep(POLL_INTERVAL_S)

    mode = job_data["mode"]
    results_path = getattr(args, "output", None) or VERIFIED_DIR / f"batch_{mode}_{job_file.stem}.jsonl"
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
            save_job(job_file, job_data)
            print(f"  {label}: {len(missing)} requested outputs missing; writing no-output records")
        for custom_id in expected_ids:
            value = results.get(custom_id)
            if isinstance(value, str):
                generated, error = value, ""
            else:
                generated = ""
                error = (value.get("error") if isinstance(value, dict) else None) or "; ".join(info.get("errors", ())) or "provider returned no output"
            m = meta.get(custom_id, {})
            if profile:
                row = completion_record(m, model_cfg, generated)
                if error:
                    row["translate_error"] = error
                if job_data.get("run_id"):
                    row["generation_run_id"] = job_data["run_id"]
                records.append(row)
                continue
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
                translate_error=error,
                sample_idx=int(m.get("_sample_idx", 0)),
                temperature=float(m.get("_temperature", 0.0)),
                custom_id=custom_id,
            ))
            if job_data.get("run_id"):
                records[-1]["generation_run_id"] = job_data["run_id"]

    print(f"\nVerifying and writing {len(records)} records to {results_path} ...")
    # Batch outputs enter the same verifier path as generated JSONL files
    verify_translation_records(records, results_path, workers=args.workers, profile=profile)

    if terminal_errors:
        raise SystemExit(
            "Batch collection stopped because one or more provider jobs failed:\n"
            + "\n".join(f"- {msg}" for msg in terminal_errors)
        )

    print(f"\nDone. Results: {results_path}")


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(prog="batch_run")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_submit = sub.add_parser("submit", help="Submit batch jobs")
    p_submit.add_argument("--job-file", type=Path, help="durable job plan; reuse this path to resume submission")
    replay = p_submit.add_mutually_exclusive_group()
    replay.add_argument("--responses", type=Path, help="prerecorded JSON object mapping request ID to response text")
    replay.add_argument("--candidate", type=Path, help="prerecorded response for one fixed completion")
    p_submit.add_argument("--recover-batch", action="append", default=[], metavar="LABEL=ID",
                          help="record the provider ID for an interrupted remote submission")
    p_submit.add_argument("--retry-unconfirmed", action="append", default=[], metavar="LABEL",
                          help="resubmit a chunk after checking that the provider did not accept its original request")
    p_submit.add_argument("--task-manifest", default="completion.json", help="reviewed project-relative completion manifest")
    p_submit.add_argument("--completion-lock", type=Path, help="select the curated proof task in this environment")
    p_submit.add_argument("--mode",    choices=["stmts", "proofs"], default="stmts",
                          help="Translate statements or full proofs (default: stmts)")
    p_submit.add_argument("--sources", help="Comma-separated benchmark names (default: all)")
    p_submit.add_argument("--corpus", choices=["extended", "published", "proofs"])
    p_submit.add_argument("--src", help="Filter to one source prover")
    p_submit.add_argument("--tgt", help="Filter to one target prover")
    p_submit.add_argument("--dry-run", action="store_true", help="Preview selection and first prompt without submitting")
    p_submit.add_argument("--ids",     help="Comma-separated theorem IDs to include (default: all)")
    p_submit.add_argument(
        "--subset",
        help="Path to a subset JSON file (list of {source,theorem_id}) to restrict evaluation",
    )
    p_submit.add_argument("--models",  help="Comma-separated model labels (default: all with a batch transport)")

    p_collect = sub.add_parser("collect", help="Poll, verify, and write results")
    p_collect.add_argument("--output", type=Path, help="result JSONL path for collection or resume")
    p_collect.add_argument("--task-manifest", default="completion.json")
    p_collect.add_argument("--completion-lock", type=Path, help="trusted environment used at submission")
    p_collect.add_argument("job_file", help="Path to the .json job file from submit")
    p_collect.add_argument("--workers", type=int, default=8,
                           help="Parallel verification workers (default: 8)")

    args = parser.parse_args(argv)
    if args.cmd == "submit":
        cmd_submit(args)
    else:
        cmd_collect(args)


if __name__ == "__main__":
    main()
