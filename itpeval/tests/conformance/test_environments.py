"""Identity, source resolution and cache publication regressions."""
import json
import subprocess
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from threading import Event
from unittest.mock import patch

from itpeval.environments import load_project, prepare_manifest, prepare_project
from itpeval.environments.cache import hash_index, inventory


class EnvironmentContracts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "proof.mm").write_text("first")
        self.prefix = self.root / "prefix"
        self.payload = self.prefix / "metamath/bin/metamath"
        self.payload.parent.mkdir(parents=True)
        # Fixtures use the adapter's version command. The contents of its
        # launcher must stay in the identity even when the version text matches.
        self.payload.write_text("#!/bin/sh\necho 'Metamath test fixture'\n")
        self.payload.chmod(0o755)
        self.cache = self.root / "cache"

    def prepare(self):
        return prepare_project("metamath", self.project, prefix=self.prefix, cache=self.cache)

    def test_same_tick_edits_are_rehashed_until_the_timestamp_settles(self):
        path = self.project / "proof.mm"
        info = path.stat()
        with (hash_index(self.cache) as db,
              patch.object(Path, "lstat", return_value=info),
              patch.object(Path, "stat", return_value=info)):
            tick = max(info.st_ctime_ns, info.st_mtime_ns)
            with patch("itpeval.environments.cache.time_ns", return_value=tick):
                first = inventory(path, db)
                path.write_text("other")
                second = inventory(path, db)
                self.assertNotEqual(first, second)
            with patch("itpeval.environments.cache.time_ns", return_value=tick + 3_000_000_000):
                self.assertEqual(inventory(path, db), second)
                with patch("itpeval.environments.cache.sha256", side_effect=AssertionError("unexpected rehash")):
                    self.assertEqual(inventory(path, db), second)

    def test_warm_index_avoids_sqlite_and_detects_a_stable_file_replacement(self):
        source = self.project / "proof.mm"
        info = source.stat()
        tick = max(info.st_ctime_ns, info.st_mtime_ns) + 3_000_000_000
        with patch("itpeval.environments.cache.time_ns", return_value=tick):
            with hash_index(self.cache) as db:
                first = inventory(source, db)
            with (patch("itpeval.environments.cache.sqlite3.connect", side_effect=AssertionError("unexpected SQLite")),
                  hash_index(self.cache) as db):
                self.assertEqual(inventory(source, db), first)
        replacement = self.project / "same-size"
        replacement.write_text("other")
        replacement.replace(source)
        metadata = source.stat()
        tick = max(metadata.st_ctime_ns, metadata.st_mtime_ns) + 3_000_000_000
        with (patch("itpeval.environments.cache.time_ns", return_value=tick),
              hash_index(self.cache) as db):
            self.assertNotEqual(inventory(source, db), first)

    def test_hashing_does_not_hold_the_sqlite_writer_lock(self):
        first = self.project / "proof.mm"
        second = self.project / "other.mm"
        second.write_text("other")
        tick = max(first.stat().st_ctime_ns, second.stat().st_ctime_ns) + 3_000_000_000
        ready = Event()
        finished = Event()

        def slow_inventory():
            with hash_index(self.cache) as db:
                inventory(first, db)
                ready.set()
                self.assertTrue(finished.wait(5))

        def finish_inventory():
            self.assertTrue(ready.wait(5))
            with hash_index(self.cache) as db:
                inventory(second, db)
            finished.set()

        with (patch("itpeval.environments.cache.time_ns", return_value=tick),
              ThreadPoolExecutor(2) as pool):
            slow = pool.submit(slow_inventory)
            fast = pool.submit(finish_inventory)
            fast.result()
            slow.result()

    def test_snapshots_bind_contents_and_detect_runtime_drift(self):
        original = self.prepare()
        self.assertEqual(load_project(original.lock_path).spec, original.spec)
        (self.project / "proof.mm").write_text("second")
        other = self.prepare()
        self.assertNotEqual(original.environment_id, other.environment_id)
        self.assertEqual((original.project / "proof.mm").read_text(), "first")
        self.payload.write_text(self.payload.read_text() + "# new build\n")
        with self.assertRaisesRegex(ValueError, "toolchain"):
            original.validate()
        self.assertNotEqual(self.prepare().environment_id, other.environment_id)

    def test_declared_import_locks_the_exact_library_file(self):
        library = self.root / "library"
        library.mkdir()
        (library / "base.mm").write_text("pinned source")
        options = {"prefix": self.prefix, "cache": self.cache, "libraries": {"set": library}, "imports": ("Base",)}
        with self.assertRaisesRegex(ValueError, "cannot resolve import"):
            prepare_project("metamath", self.project, **options)
        env = prepare_project("metamath", self.project, import_bindings={"Base": ("library/set", "base.mm")},
                              **options)
        self.assertEqual(env.spec.resolved_imports[0][:3], ("Base", "library/set", "base.mm"))
        self.assertEqual(load_project(env.lock_path).spec, env.spec)

    def test_concurrent_publish_and_snapshot_drift(self):
        with ThreadPoolExecutor(3) as pool:
            envs = list(pool.map(lambda _: self.prepare(), range(3)))
        self.assertEqual(len({env.lock_path for env in envs}), 1)
        snapshot = envs[0].project / "proof.mm"
        snapshot.chmod(0o644)
        snapshot.write_text("tampered")
        with self.assertRaisesRegex(ValueError, "content"):
            load_project(envs[0].lock_path)

    def test_floating_git_ref_resolves_and_pinned_commit_replays(self):
        repo = self.project
        def git(*args):
            return subprocess.check_output(["git", "-C", repo, *args], text=True).strip()
        git("init", "-q")
        git("symbolic-ref", "HEAD", "refs/heads/release")
        git("add", "proof.mm")
        def commit(message):
            git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid",
                "commit", "-qm", message)
            return git("rev-parse", "HEAD")
        first = commit("first")
        path = self.root / "project.json"
        def resolve(ref):
            path.write_text(json.dumps({"schema_version": 1, "name": "example", "prover": "metamath",
                                        "project": {"url": str(repo), "revision": ref}}))
            return prepare_manifest(path, prefix=self.prefix, cache=self.cache)
        locked = resolve("refs/heads/release")
        self.assertEqual(locked.spec.project_commit, first)
        (repo / "proof.mm").write_text("second")
        git("add", "proof.mm")
        second = commit("second")
        self.assertEqual(resolve("release").spec.project_commit, second)
        repo.rename(self.root / "offline")
        self.assertEqual(resolve(first).environment_id, locked.environment_id)
        self.assertEqual((load_project(locked.lock_path).project / "proof.mm").read_text(), "first")

    def test_manifest_pins_optional_native_tools_and_detects_drift(self):
        path = self.root / "environment.json"
        instrument = self.prefix / "auxiliary" / "instrument"
        instrument.parent.mkdir()
        instrument.write_text("tool version 1")
        manifest = {"schema_version": 1, "prover": "metamath", "name": "release",
                    "project": {"path": "project"},
                    "toolchain_inputs": {"instrument": {"prefix_path": "auxiliary/instrument"}}}
        path.write_text(json.dumps(manifest))
        env = prepare_manifest(path, prefix=self.prefix, cache=self.cache)
        self.assertEqual(dict(env.extra_inputs)["external/instrument"], instrument)
        self.assertEqual(load_project(env.lock_path).environment_id, env.environment_id)
        instrument.write_text("tool version 2")
        with self.assertRaisesRegex(ValueError, "toolchain"):
            load_project(env.lock_path)
        for bad in ({**manifest, "schema_version": True}, {**manifest, "project": None},
                    {**manifest, "imports": "Base"}, {**manifest, "toolchain_inputs": {"t": {"prefix_path": "../x"}}}):
            path.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):
                prepare_manifest(path, prefix=self.prefix, cache=self.cache)


if __name__ == "__main__":
    unittest.main()
