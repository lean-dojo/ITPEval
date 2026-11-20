from __future__ import annotations

import fcntl
import json
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterable, TypeVar

T = TypeVar("T", bound=dict)


def load_jsonl(path: Path) -> list[dict]:
    records: list[dict] = []
    if not path.exists():
        return records
    # Invalid JSONL is treated as a data error instead of being silently skipped
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError as e:
                raise ValueError(f"{path}:{lineno}: invalid JSONL: {e}") from e
    return records


def load_checkpoint(path: Path, key_fn: Callable[[dict], str]) -> dict[str, dict]:
    # Later checkpoint rows replace earlier rows with the same key
    return {key_fn(r): r for r in load_jsonl(path)}


def write_jsonl_atomic(path: Path, records: Iterable[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_suffix(path.suffix + ".tmp")
    # Write the final ordered file only after all rows are ready
    with tmp_path.open("w", encoding="utf-8") as f:
        for record in records:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
    tmp_path.replace(path)


def repair_tail(path: Path) -> None:
    """Discard one torn final append to an owned, manifest-bound output."""
    if not path.exists() or path.stat().st_size == 0:
        return
    with path.open("r+b") as stream:
        stream.seek(-1, 2)
        if stream.read() == b"\n":
            return
        position = stream.tell()
        while position:
            start = max(position - 65536, 0)
            stream.seek(start)
            split = stream.read(position - start).rfind(b"\n")
            if split >= 0:
                position = start + split + 1
                break
            position = start
        stream.seek(position)
        tail = stream.read()
        try:
            json.loads(tail)
        except (json.JSONDecodeError, UnicodeDecodeError):
            print(f"Ignoring incomplete final checkpoint row in {path}", flush=True)
            stream.truncate(position)
        else:
            stream.write(b"\n")


@contextmanager
def result_writer(path: Path):
    """Serialize jobs that select the same output and run manifest."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_suffix(path.suffix + ".lock").open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield
