"""Regression coverage for reusable backend dispatch and concurrent CLI runs."""
import json
import os
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli import lib
from itpeval.environments import prepare_project
from itpeval.itp import run_itp


class CliRunDirectories(unittest.TestCase):
    def test_simultaneous_runs_get_separate_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch.object(lib, "RUNS_ROOT", root), patch.object(lib, "utc_timestamp", return_value="same-second"):
                with ThreadPoolExecutor(12) as pool:
                    paths = list(pool.map(lambda n: lib.create_run_dir("check", root, str(n)), range(40)))
            self.assertEqual(len(set(paths)), 40)
            for n, path in enumerate(paths):
                self.assertEqual(json.loads((path / "meta.json").read_bytes())["task"], str(n))


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_METAMATH"), "requires native Metamath")
class BackendInterface(unittest.TestCase):
    def test_locked_project_through_registry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env = prepare_project("metamath", curated_project("metamath"), prefix=lib.default_prefix(), cache=root)
            backend = get_backend("metamath")
            task = backend.build_task(env)
            result = backend.inspect_declarations(env, task.artifact.entrypoint, root / "bundles")
            self.assertGreater(result.report["declarations"], 1)
            session = backend.open_document(task, prepared=env)
            handle, evidence = session.submit(session.handle, task.allowed_edits[0])
            self.assertTrue(evidence.task_success, evidence.stderr)
            self.assertEqual(evidence.artifact_id, session.finalize(handle).artifact_id)
            original = run_itp(task=task, candidate=task.allowed_edits[0], prepared=env)
            self.assertEqual((original.task_success, original.artifact_id), (True, evidence.artifact_id))
            with self.assertRaisesRegex(ValueError, "own artifact"):
                run_itp(task=task, candidate=task.allowed_edits[0], prepared=env, timeout_s=1)
            with self.assertRaisesRegex(ValueError, "another backend"):
                get_backend("mizar").open_document(task, prepared=env)
