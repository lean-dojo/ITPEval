"""Resolve the released benchmark data independently of the Python installation."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path
from urllib.request import urlopen

PACKAGE = Path(__file__).resolve().parent
LOCK = PACKAGE / "benchmark-lock.json"


def _cache_root() -> Path:
    home = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return home / "itpeval" / "datasets" / _lock()["revision"]


def _lock() -> dict:
    return json.loads(LOCK.read_text(encoding="utf-8"))


def data_root() -> Path:
    if "ITPEVAL_DATA_DIR" in os.environ:
        return Path(os.environ["ITPEVAL_DATA_DIR"]).expanduser().resolve()
    local = PACKAGE / "data"
    if (local / "proofs.json").is_file():
        return local
    return _cache_root() / "eval/data"


def logipedia_index() -> Path:
    return data_root().parents[1] / "data/logipedia/data/index.json"


def materialize(destination: Path, source_checkout: Path | None = None) -> Path:
    """Install the frozen files into a cache; validate each file before replacing it."""
    lock = _lock()
    for relative, checksum in lock["files"].items():
        target = destination / relative
        if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() == checksum:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        if source_checkout is None:
            source = urlopen(f"https://raw.githubusercontent.com/lean-dojo/ITPEval/{lock['revision']}/{relative}", timeout=120)
        else:
            source = (source_checkout / relative).open("rb")
        with source, tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as tmp:
            staging = Path(tmp.name)
            try:
                shutil.copyfileobj(source, tmp)
                tmp.flush()
                if hashlib.sha256(staging.read_bytes()).hexdigest() != checksum:
                    raise ValueError(f"benchmark checksum mismatch for {relative}")
                staging.replace(target)
            finally:
                staging.unlink(missing_ok=True)
    return destination / "eval/data"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, default=_cache_root())
    parser.add_argument("--from-checkout", type=Path, help="read released bytes from this checkout")
    args = parser.parse_args()
    print(materialize(args.destination.resolve(), args.from_checkout))


if __name__ == "__main__":
    main()
