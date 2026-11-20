"""Transport native observations without parsing a prover's interactive display."""
from __future__ import annotations

import json
import os
from pathlib import Path

NATIVE = Path(__file__).with_name("native")


def probe_environment(ctx, **extra):
    env = {k: os.environ[k] for k in ("PATH", "HOME", "USER", "LANG") if k in os.environ}
    env.update(ctx.prepared.environment)
    return {**env, **{k: str(v) for k, v in extra.items()}}


def observations(path: Path):
    """Some REPLs exit zero after a fatal ML/Lisp error. Require a final receipt."""
    if not path.is_file():
        raise ValueError("native inspector did not write its observations")
    try:
        rows = [[bytes.fromhex(col).decode("utf-8") for col in line.split("\t")]
                for line in path.read_text("ascii").splitlines()]
    except (UnicodeError, ValueError) as exc:
        raise ValueError("invalid native observation encoding") from exc
    if not rows or rows.pop() != ["done"]:
        raise ValueError("native inspector did not complete")
    return rows


def evidence(ctx, row):
    return ctx.evidence(json.dumps(row, ensure_ascii=False, separators=(",", ":")).encode())


def line_span(source: bytes, first: int, last: int, col=0, end_col=None):
    """Convert one-based lines and zero-based character columns to UTF-8 bytes."""
    lines = source.decode("utf-8").splitlines(keepends=True)
    if not 1 <= first <= last <= len(lines):
        raise ValueError(f"native source position outside file: {first}..{last}")
    start = sum(len(s.encode()) for s in lines[:first - 1])
    end = start + sum(len(s.encode()) for s in lines[first - 1:last - 1])
    return start + len(lines[first - 1][:col].encode()), end + len(lines[last - 1][:end_col].encode())
