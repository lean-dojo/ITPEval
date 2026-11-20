from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import nullcontext
from datetime import datetime
from pathlib import Path
from uuid import uuid4

from eval.pipeline.config import VERIFIED_DIR, GENERATED_DIR
from eval.pipeline.jsonl import load_jsonl, repair_tail, result_writer
from eval.pipeline.manifests import translation_manifest
from eval.pipeline.models import select_models
from eval.pipeline.records import make_translation_record, translation_custom_id, translation_record_key
from itpeval.core.records import digest
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.prompt import build_prompt
from eval.pipeline.translate import translate
from eval.pipeline.verify import failed_verification, verify_translation_record


def _run_single(
    *,
    model_cfg: dict,
    pair: dict,
    sample_idx: int,
    mode: str,
    temperature: float,
    max_tokens: int,
    job_num: int,
    total: int,
    no_verify: bool = False,
    responses: dict | None = None,
) -> dict:
    system_prompt, user_prompt = build_prompt(
        title=pair["title"],
        src_prover=pair["src_prover"],
        tgt_prover=pair["tgt_prover"],
        source_content=pair["src_content"],
        mode=mode,
    )
    src_prover = pair["src_prover"]
    tgt_prover = pair["tgt_prover"]

    label = (
        f"[{job_num}/{total}] "
        f"thm={pair['theorem_id']:3d} "
        f"{src_prover}→{tgt_prover} "
        f"model={model_cfg['label']}"
    )
    if total > 1:
        label += f" sample={sample_idx+1}"
    print(label, flush=True)

    t0 = time.monotonic()
    try:
        if responses is not None:
            generated = responses.get(translation_custom_id(pair, sample_idx=sample_idx))
            if not isinstance(generated, str):
                raise ValueError("prerecorded transport returned no output for this request")
        else:
            generated = translate(
                system_prompt=system_prompt, user_prompt=user_prompt, model_cfg=model_cfg,
                temperature=temperature, max_tokens=max_tokens)
        translate_ms = int((time.monotonic() - t0) * 1000)
        translate_error = ""
    except Exception as e:
        generated = ""
        translate_ms = int((time.monotonic() - t0) * 1000)
        translate_error = str(e)
        print(f"  [translate error] {label}: {e}", flush=True)

    record = make_translation_record(
        pair=pair, model_cfg=model_cfg, mode=mode, generated=generated,
        translate_error=translate_error, verify_error=translate_error,
        translate_ms=translate_ms, sample_idx=sample_idx, temperature=temperature,
    )
    if not no_verify:
        try:
            record = verify_translation_record(record)
        except Exception as error:
            record = failed_verification(record, error)

    if no_verify:
        status = "OK" if generated else "FAIL"
        print(f"  {status}  {label}  translate={translate_ms}ms", flush=True)
    else:
        status = "PASS" if record["verified"] else "FAIL"
        print(f"  {status}  {label}  translate={translate_ms}ms  verify={record['verify_ms']}ms", flush=True)
    return record


def _load_done(results_path: Path, run_id: str | None = None) -> set[str]:
    rows = load_jsonl(results_path)
    if run_id is not None and any(row.get("run_id") != run_id for row in rows):
        raise ValueError("saved records differ from generation run manifest")
    return {translation_record_key(r) for r in rows}


def run_eval(
    *,
    models: list[dict],
    pairs: list[dict],
    mode: str,
    dry_run: bool,
    results_path: Path,
    max_src_chars: int | None,
    k: int,
    temperature: float,
    max_tokens: int = 16000,
    workers: int = 1,
    no_verify: bool = False,
    responses: dict | None = None,
) -> None:
    if workers < 1 or k < 1:
        raise ValueError("sample count and worker count must be positive")
    filtered = pairs if max_src_chars is None else [
        p for p in pairs if len(p["src_content"]) <= max_src_chars
    ]
    skipped = len(pairs) - len(filtered)
    if skipped:
        print(f"  ({skipped} pairs skipped: source > {max_src_chars} chars)")

    jobs = [
        (m, p, s)
        for m in models
        for p in filtered
        for s in range(k)
    ]
    if responses is not None:
        ids = {translation_custom_id(pair, sample_idx=sample) for _, pair, sample in jobs}
        if (not isinstance(responses, dict) or responses.keys() - ids or
                any(value is not None and not isinstance(value, str) for value in responses.values())):
            raise ValueError("prerecorded responses must map selected request IDs to raw text or null")

    with result_writer(results_path) if not dry_run else nullcontext():
        if not dry_run:
            manifest = translation_manifest(models, filtered, mode, k, temperature, max_tokens, no_verify)
            manifest.bind(results_path)
            repair_tail(results_path)
        done = _load_done(results_path, manifest.run_id if not dry_run else None)
        if done:
            # Resume skips records using the same key used by post-hoc verification
            jobs = [
                (m, p, s) for m, p, s in jobs
                if translation_record_key(make_translation_record(
                    pair=p,
                    model_cfg=m,
                    mode=mode,
                    sample_idx=s,
                    temperature=temperature,
                )) not in done
            ]
            print(f"  Resuming: {len(done)} already done, {len(jobs)} remaining")

        total = len(jobs)

        if dry_run:
            # Dry runs print prompt previews without calling provider APIs or provers
            for i, (model_cfg, pair, sample_idx) in enumerate(jobs, 1):
                system_prompt, user_prompt = build_prompt(
                    title=pair["title"],
                    src_prover=pair["src_prover"],
                    tgt_prover=pair["tgt_prover"],
                    source_content=pair["src_content"],
                    mode=mode,
                )
                print(f"[{i}/{total}] thm={pair['theorem_id']:3d} {pair['src_prover']}→{pair['tgt_prover']} model={model_cfg['label']}")
                print(f"  [dry-run] system: {system_prompt[:80]}...")
                print(f"  [dry-run] user:   {user_prompt[:80]}...")
            return

        with results_path.open("a", encoding="utf-8") as out:
            with ThreadPoolExecutor(max_workers=workers) as executor:
                futures = {
                    executor.submit(
                        _run_single,
                        model_cfg=model_cfg,
                        pair=pair,
                        sample_idx=sample_idx,
                        mode=mode,
                        temperature=temperature,
                        max_tokens=max_tokens,
                        job_num=i,
                        total=total,
                        no_verify=no_verify,
                        responses=responses,
                    ): (model_cfg, pair, sample_idx)
                    for i, (model_cfg, pair, sample_idx) in enumerate(jobs, 1)
                }
                for future in as_completed(futures):
                    try:
                        record = future.result()
                    except Exception as e:
                        print(f"  [job error] {e}", flush=True)
                        model_cfg, pair, sample_idx = futures[future]
                        record = make_translation_record(pair=pair, model_cfg=model_cfg, mode=mode,
                            sample_idx=sample_idx, temperature=temperature, verify_error=str(e))
                        record["execution_outcome"] = "infrastructure_error"
                    record["run_id"] = manifest.run_id
                    out.write(json.dumps(record, ensure_ascii=False) + "\n")
                    out.flush()


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--model",         help="Model label(s), comma-separated (default: all)")
    parser.add_argument("--responses", type=Path, help="generate from a JSON object mapping request IDs to raw text")
    parser.add_argument("--mode",          choices=["stmts", "proofs"], default="stmts",
                        help="Translate statements or full proofs (default: stmts)")
    parser.add_argument("--sources",       help="Benchmark sources, comma-separated (default: all)")
    parser.add_argument("--corpus", choices=["extended", "published", "proofs"],
                        help="select the archived four-prover statement population with published")
    parser.add_argument("--output", type=Path, help="result path for a new generation run")
    parser.add_argument("--src",           help="Filter to this source prover")
    parser.add_argument("--tgt",           help="Filter to this target prover")
    parser.add_argument("--ids",           help="Theorem IDs, comma-separated (default: all)")
    parser.add_argument(
        "--subset",
        help="Path to a subset JSON file (list of {source,theorem_id}) to restrict evaluation",
    )
    parser.add_argument("--max-src-chars", type=int, default=None,
                        help="Skip pairs whose source exceeds this many chars")
    parser.add_argument("--k",             type=int, default=1,
                        help="Number of samples per pair for pass@k (default: 1)")
    parser.add_argument("--temperature",   type=float, default=0.0,
                        help="Sampling temperature; use >0 with --k>1 (default: 0.0)")
    parser.add_argument("--max-tokens",     type=int, default=16000,
                        help="Max output tokens per call (default: 16000)")
    parser.add_argument("--workers",        type=int, default=1,
                        help="Number of parallel translation workers (default: 1)")
    parser.add_argument("--no-verify",      action="store_true",
                        help="Generate translations but skip verification")
    parser.add_argument("--resume",         metavar="PATH",
                        help="Resume from an existing results JSONL, skipping completed jobs")
    parser.add_argument("--dry-run",       action="store_true",
                        help="Print prompts, skip API + verify")
    args = parser.parse_args(argv)

    responses = json.loads(args.responses.read_bytes()) if args.responses else None
    if args.responses:
        if args.model:
            parser.error("--responses and --model select different generation transports")
        models = [{"label": "prerecorded", "provider": "prerecorded", "id": digest(responses)}]
    else:
        models = select_models(args.model)

    sources = args.sources.split(",") if args.sources else None
    ids = [int(x) for x in args.ids.split(",")] if args.ids else None
    subset = None
    if args.subset:
        subset_items = json.loads(Path(args.subset).read_text(encoding="utf-8"))
        subset = {(it["source"], int(it["theorem_id"])) for it in subset_items}
    pairs = load_pairs(args.mode, sources=sources, theorem_ids=ids, subset=subset, corpus=args.corpus)
    if args.src:
        pairs = [p for p in pairs if p["src_prover"] == args.src]
    if args.tgt:
        pairs = [p for p in pairs if p["tgt_prover"] == args.tgt]

    if args.resume:
        if args.output:
            parser.error("--output and --resume select the same destination; provide one")
        results_path = Path(args.resume)
        if not results_path.exists():
            sys.exit(f"Resume file not found: {results_path}")
    elif args.output:
        results_path = args.output
    else:
        out_dir = GENERATED_DIR if args.no_verify else VERIFIED_DIR
        if not args.dry_run:
            out_dir.mkdir(parents=True, exist_ok=True)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        model_tag = args.model.replace(",", "+") if args.model else "all"
        results_path = out_dir / f"{model_tag}_{args.mode}_{timestamp}_{uuid4().hex[:8]}.jsonl"
    print(f"Writing results to {results_path}")
    print(
        f"  {len(pairs)} pairs × {len(models)} models × k={args.k}"
        f" = up to {len(pairs) * len(models) * args.k} runs\n"
    )

    run_eval(
        models=models,
        pairs=pairs,
        mode=args.mode,
        dry_run=args.dry_run,
        results_path=results_path,
        max_src_chars=args.max_src_chars,
        k=args.k,
        temperature=args.temperature,
        max_tokens=args.max_tokens,
        workers=args.workers,
        no_verify=args.no_verify,
        responses=responses,
    )

    print(f"\nDone. Results: {results_path}")


if __name__ == "__main__":
    main()
