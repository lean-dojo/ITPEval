from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


PROVERS = Path(__file__).resolve().parents[1] / "provers"


class NativeEnvironmentTests(unittest.TestCase):
    def test_lean_accepts_prebuilt_mathlib_in_toml_project(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task = root / "task"
            task.mkdir()
            (task / "Hello.lean").write_text("import Mathlib\n#check Nat\n")
            lean = root / "prefix/lean4"
            (lean / "bin").mkdir(parents=True)
            for name in ("lean", "lake"):
                executable = lean / "bin" / name
                executable.write_text(f'#!/bin/sh\nprintf "{name} called\\n"\n')
                executable.chmod(0o755)
            project = lean / "mathlib-project"
            olean = project / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
            olean.parent.mkdir(parents=True)
            olean.touch()
            (project / "lakefile.toml").write_text('name = "fixture"\n')
            env = {k: v for k, v in os.environ.items() if not k.startswith("ITPEVAL_LEAN4_")}
            env.update(ITPEVAL_PREFIX=str(root / "prefix"), ITPEVAL_TASK_DIR=str(task))
            result = subprocess.run(["/bin/bash", str(PROVERS / "lean4/check.sh")], env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("lake called", result.stdout)

    def test_parallel_isabelle_checks_use_separate_cleaned_user_homes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task = root / "task"
            task.mkdir()
            (task / "ROOT").write_text('session "ITPEval_Hello" = HOL +\n  theories Hello\n')
            (task / "Hello.thy").write_text("theory Hello imports Main begin\nlemma t: True sorry\nend\n")
            executable = root / "prefix/isabelle/bin/isabelle"
            executable.parent.mkdir(parents=True)
            executable.write_text('#!/bin/sh\nprintf "%s\\n" "$USER_HOME"\nmkdir "$USER_HOME/active-check"\nsleep 0.1\n')
            executable.chmod(0o755)
            env = {k: v for k, v in os.environ.items() if k != "ITPEVAL_ISABELLE_USER_HOME"}
            env.update(ITPEVAL_PREFIX=str(root / "prefix"), ITPEVAL_TASK_DIR=str(task))
            def run():
                return subprocess.run(["/bin/bash", str(PROVERS / "isabelle/check.sh")], env=env, capture_output=True, text=True)
            with ThreadPoolExecutor(max_workers=2) as pool:
                results = list(pool.map(lambda _: run(), range(2)))
            for result in results:
                self.assertEqual(result.returncode, 0, result.stderr)
            homes = [r.stdout.strip() for r in results]
            self.assertNotEqual(*homes)
            for path in homes:
                self.assertFalse(Path(path).exists())


if __name__ == "__main__":
    unittest.main()
