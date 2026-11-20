from __future__ import annotations

import argparse
import json
from pathlib import Path

from eval.pipeline.jsonl import load_jsonl
from eval.pipeline.config import VERIFIED_DIR
from eval.pipeline.verify import verify_translation_records
from eval.pipeline.task_profile import TaskProfile


def _verify_file(
    input_path: Path,
    workers: int,
    *,
    hol_light_timeout_s: int | None,
    profile: TaskProfile | None = None,
    output_dir: Path | None = None,
) -> Path:
    records = load_jsonl(input_path)
    total = len(records)
    print(f"{input_path.name}: {total} entries")

    out_path = (output_dir or VERIFIED_DIR) / input_path.name
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Post-hoc verification shares checkpointing and schema handling with batch collect
    verify_translation_records(
        records,
        out_path,
        profile=profile,
        workers=workers,
        hol_light_timeout_s=hol_light_timeout_s,
    )

    passed = sum(
        1 for l in out_path.read_text().splitlines()
        if l.strip() and json.loads(l).get("verified")
    )
    print(f"\n{input_path.name}: {passed}/{total} passed")
    print(f"Output: {out_path}")
    return out_path


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, help="destination for verified files and checkpoints")
    parser.add_argument("--completion-lock", type=Path, help="trusted environment for completion records")
    parser.add_argument("--task-manifest", default="completion.json")
    parser.add_argument("files", nargs="+", help="Generated JSONL files to verify")
    parser.add_argument("--workers", type=int, default=8,
                        help="Parallel verification workers (default: 8)")
    parser.add_argument(
        "--hol-light-timeout-s",
        type=int,
        default=None,
        help="Override per-entry HOL Light timeout in seconds (default: 300).",
    )
    args = parser.parse_args(argv)

    profile = TaskProfile.from_lock(args.completion_lock, args.task_manifest) if args.completion_lock else None
    for f in args.files:
        _verify_file(
            Path(f),
            args.workers,
            hol_light_timeout_s=args.hol_light_timeout_s,
            profile=profile, output_dir=args.output_dir,
        )


if __name__ == "__main__":
    main()
