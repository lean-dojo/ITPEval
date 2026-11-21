"""Local content store. Only fully written snapshots become visible to readers."""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import sqlite3
import stat
import tempfile
from contextlib import contextmanager
from pathlib import Path
from threading import Lock
from time import time_ns

from itpeval.core.records import digest


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False,
                                     encoding="utf-8") as stream:
        try:
            json.dump(value, stream, sort_keys=True, indent=2, ensure_ascii=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
            os.replace(stream.name, path)
        finally:
            Path(stream.name).unlink(missing_ok=True)


_MEMORY_HASH_LIMIT = 65_536
_memory_hashes = {}
_memory_hashes_lock = Lock()


def _remember_hash(key, value):
    with _memory_hashes_lock:
        # Hot checks normally revisit a small set of installations. Bound the
        # cache when a process also traverses many independent library trees.
        if len(_memory_hashes) >= _MEMORY_HASH_LIMIT:
            _memory_hashes.clear()
        _memory_hashes[key] = value


def _disk_key(identity):
    # v2 excludes entries computed before the same-timestamp write guard.
    return "v2:" + ":".join(map(str, identity))


class _HashIndex:
    def __init__(self, cache):
        self.cache = cache
        self.cache_key = os.fspath(cache)
        self.db = None
        self.pending = {}

    def _connect(self):
        if self.db is None:
            self.cache.mkdir(parents=True, exist_ok=True)
            db = sqlite3.connect(self.cache / "file-hashes.sqlite3", timeout=120)
            try:
                # The initial WAL transition can return BUSY before
                # SQLite's busy_timeout applies.
                with (self.cache / "initialize.lock").open("a") as initialize:
                    fcntl.flock(initialize, fcntl.LOCK_EX)
                    if db.execute("PRAGMA journal_mode").fetchone()[0] != "wal":
                        db.execute("PRAGMA journal_mode=WAL")
                    db.execute("CREATE TABLE IF NOT EXISTS files (identity TEXT PRIMARY KEY, sha256 TEXT NOT NULL)")
            except BaseException:
                db.close()
                raise
            self.db = db
        return self.db

    def lookup(self, identity):
        key = (self.cache_key, identity)
        value = _memory_hashes.get(key)
        if value is None:
            value = self.pending.get(identity)
        if value is None:
            row = self._connect().execute("SELECT sha256 FROM files WHERE identity=?", (_disk_key(identity),)).fetchone()
            if row:
                value = row[0]
                _remember_hash(key, value)
        return value

    def store(self, identity, value):
        self.pending[identity] = value
        _remember_hash((self.cache_key, identity), value)

    def finish(self):
        if self.pending:
            db = self._connect()
            # Write only after the inventory. A worker never holds the SQLite
            # writer lock while walking the tree or calling a version probe.
            db.executemany("INSERT OR IGNORE INTO files VALUES (?,?)",
                           ((_disk_key(identity), value) for identity, value in self.pending.items()))
            db.commit()


@contextmanager
def hash_index(cache: Path):
    """Memoize stable stat identities in memory and share them on disk."""
    index = _HashIndex(cache.resolve())
    try:
        yield index
        index.finish()
    finally:
        if index.db is not None:
            index.db.close()


def _file_record(path: Path, info, db, stable_before: int):
    identity = (info.st_dev, info.st_ino, info.st_ctime_ns, info.st_mtime_ns,
                info.st_size, info.st_mode)
    stable = info.st_ctime_ns < stable_before and info.st_mtime_ns < stable_before
    if stable:
        value = db.lookup(identity)
        if value is not None:
            return value
    path = Path(path)
    h = sha256(path)
    end = path.stat()
    if (info.st_ino, info.st_dev, info.st_ctime_ns) != (end.st_ino, end.st_dev, end.st_ctime_ns):
        raise ValueError(f"input changed while hashing {path}")
    if stable:
        db.store(identity, h)
    return h


def inventory(root: Path, db, *, native: bool = False) -> dict:
    """Inventory regular files, directories, executable bits and native symlinks.

    Native distributions often link their public binaries and libraries. Follow
    those links as dependencies. Source snapshots require explicit files and
    directories so materialization cannot accidentally depend on its location.
    """
    records = {}
    # Same-size writes can share a timestamp on coarse filesystems. Read recent
    # files directly until even a two-second timestamp interval has elapsed.
    stable_before = time_ns() - 2_000_000_000

    def visit(path: Path, relative: str, parents, info):
        if stat.S_ISLNK(info.st_mode):
            if not native:
                raise ValueError(f"source symlink requires an explicit dependency: {path}")
            records[relative] = ["link", os.readlink(path)]
            try:
                target = os.path.realpath(path, strict=True)
            except FileNotFoundError:
                return
            visit(target, relative + "@", parents, os.lstat(target))
            return
        if stat.S_ISREG(info.st_mode):
            records[relative] = ["file", bool(info.st_mode & 0o111), _file_record(path, info, db, stable_before)]
        elif stat.S_ISDIR(info.st_mode):
            key = (info.st_dev, info.st_ino)
            records[relative] = ["directory"]
            if key in parents:
                return
            ancestors = parents | {key}
            # The canonical digest sorts record keys, so walks can use directory order.
            with os.scandir(path) as children:
                entries = list(children)
            for child in entries:
                if child.name != ".git":
                    visit(child.path, f"{relative}/{child.name}", ancestors,
                          child.stat(follow_symlinks=False))
        else:
            raise ValueError(f"unsupported filesystem object: {path}")

    visit(root, ".", frozenset(), root.lstat())
    return records


def snapshot(source: Path, cache: Path, db) -> tuple[Path, str]:
    """Publish a verified source tree under its content hash, including dirty files."""
    source = source.resolve(strict=True)
    if not source.is_dir() or cache.resolve().is_relative_to(source):
        raise ValueError("the source must be a directory and the cache must be outside it")
    expected = inventory(source, db)
    revision = digest(expected)
    target = cache / "sources" / revision
    if not target.is_dir():
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=target.parent) as work:
            copy = Path(work) / "source"
            shutil.copytree(source, copy, symlinks=True, ignore=shutil.ignore_patterns(".git"))
            if inventory(copy, db) != expected:
                raise ValueError(f"source changed while preparing {source}")
            for rel, fields in expected.items():
                if fields[0] == "file":
                    (copy / rel).chmod(0o555 if fields[1] else 0o444)
            try:
                copy.rename(target)
            except OSError:
                # Another preparer may have published the same content first.
                if not target.is_dir():
                    raise
    if inventory(target, db) != expected:
        raise ValueError(f"damaged snapshot at {target}")
    return target, revision
