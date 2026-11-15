from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path

from eval.pipeline.config import VERIFIED_DIR, GENERATED_DIR
from eval.pipeline.jsonl import load_jsonl
from eval.pipeline.models import select_models
from eval.pipeline.records import make_translation_record, translation_record_key
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.prompt import build_prompt
from eval.pipeline.translate import translate
from eval.pipeline.verify import verify_translation_record


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
        generated = translate(
            system_prompt=system_prompt,
            user_prompt=user_prompt,
            model_cfg=model_cfg,
            temperature=temperature,
            max_tokens=max_tokens,
        )
        translate_ms = int((time.monotonic() - t0) * 1000)
        translate_error = ""
    except Exception as e:
        generated = ""
        translate_ms = int((time.monotonic() - t0) * 1000)
        translate_error = str(e)
        print(f"  [translate error] {label}: {e}", flush=True)

    if no_verify or not generated or translate_error:
        verified = False
        verify_error = translate_error
        verify_ms = 0
    else:
        # Synchronous runs verify immediately unless --no-verify is set
        checked = verify_translation_record({"mode": mode, "tgt_prover": tgt_prover,
                                             "generated": generated})
        generated = checked["generated"]
        verified = checked["verified"]
        verify_error = checked["verify_error"]
        verify_ms = checked["verify_ms"]

    if no_verify:
        status = "OK" if generated else "FAIL"
        print(f"  {status}  {label}  translate={translate_ms}ms", flush=True)
    else:
        status = "PASS" if verified else "FAIL"
        print(f"  {status}  {label}  translate={translate_ms}ms  verify={verify_ms}ms", flush=True)

    return make_translation_record(
        pair=pair,
        model_cfg=model_cfg,
        mode=mode,
        generated=generated,
        verified=verified,
        translate_error=translate_error,
        verify_error=verify_error,
        translate_ms=translate_ms,
        verify_ms=verify_ms,
        sample_idx=sample_idx,
        temperature=temperature,
    )


def _load_done(results_path: Path) -> set[str]:
    return {translation_record_key(r) for r in load_jsonl(results_path)}


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
) -> None:
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

    done = _load_done(results_path)
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

    write_lock = threading.Lock()

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
                ): i
                for i, (model_cfg, pair, sample_idx) in enumerate(jobs, 1)
            }
            for future in as_completed(futures):
                try:
                    record = future.result()
                except Exception as e:
                    print(f"  [job error] {e}", flush=True)
                    continue
                with write_lock:
                    out.write(json.dumps(record, ensure_ascii=False) + "\n")
                    out.flush()


def main() -> None:
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--model",         help="Model label(s), comma-separated (default: all)")
    parser.add_argument("--mode",          choices=["stmts", "proofs"], default="stmts",
                        help="Translate statements or full proofs (default: stmts)")
    parser.add_argument("--sources",       help="Benchmark sources, comma-separated (default: all)")
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
    args = parser.parse_args()

    models = select_models(args.model)

    sources = args.sources.split(",") if args.sources else None
    ids = [int(x) for x in args.ids.split(",")] if args.ids else None
    subset = None
    if args.subset:
        subset_items = json.loads(Path(args.subset).read_text(encoding="utf-8"))
        subset = {(it["source"], int(it["theorem_id"])) for it in subset_items}
    pairs = load_pairs(args.mode, sources=sources, theorem_ids=ids, subset=subset)
    if args.src:
        pairs = [p for p in pairs if p["src_prover"] == args.src]
    if args.tgt:
        pairs = [p for p in pairs if p["tgt_prover"] == args.tgt]

    if args.resume:
        results_path = Path(args.resume)
        if not results_path.exists():
            sys.exit(f"Resume file not found: {results_path}")
    else:
        out_dir = GENERATED_DIR if args.no_verify else VERIFIED_DIR
        if not args.dry_run:
            out_dir.mkdir(parents=True, exist_ok=True)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        model_tag = args.model.replace(",", "+") if args.model else "all"
        results_path = out_dir / f"{model_tag}_{args.mode}_{timestamp}.jsonl"
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
    )

    print(f"\nDone. Results: {results_path}")


if __name__ == "__main__":
    main()
