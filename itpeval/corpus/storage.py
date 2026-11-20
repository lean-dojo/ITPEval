"""Content-addressed bytes and deterministic portable records."""

import hashlib
import json
import os
from pathlib import Path
from tempfile import NamedTemporaryFile


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encode(value) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                      allow_nan=False).encode("utf-8")


def object_id(*parts) -> str:
    return digest(encode(parts))


def jsonl(path, rows):
    path = Path(path)
    with NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        tmp = Path(stream.name)
        try:
            for row in rows:
                stream.write(encode(row) + b"\n")
            stream.flush()
            os.replace(tmp, path)
        finally:
            tmp.unlink(missing_ok=True)


def read_jsonl(path):
    with Path(path).open(encoding="utf-8") as stream:
        yield from map(json.loads, stream)


def store_blob(directory: Path, data: bytes) -> str:
    key = digest(data)
    path = directory / key[:2] / key[2:]
    if path.exists():
        if digest(path.read_bytes()) != key:
            raise ValueError(f"corrupt stored blob {key}")
        return key
    path.parent.mkdir(parents=True, exist_ok=True)
    with NamedTemporaryFile(dir=path.parent, delete=False) as tmp:
        tmp.write(data)
    os.replace(tmp.name, path)
    return key


def project_file(root: Path, name: str) -> Path:
    path = Path(name)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"invalid project path {name!r}")
    result = (root / path).resolve(strict=True)
    if not result.is_relative_to(root.resolve()) or not result.is_file():
        raise ValueError(f"file outside project {name!r}")
    return result
