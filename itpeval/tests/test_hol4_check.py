from __future__ import annotations

import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


class Hol4CheckTests(unittest.TestCase):
    def test_check_ignores_stale_task_build_cache(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_dir = root / "task"
            stale_cache = task_dir / ".hol" / "make-deps" / "lastmaker"
            stale_cache.parent.mkdir(parents=True)
            stale_cache.write_text("/stale/Holmake\n", encoding="utf-8")
            (task_dir / "Holmakefile").write_text(
                "THEORIES = hello\n",
                encoding="utf-8",
            )
            (task_dir / "helloScript.sml").write_text(
                "open HolKernel boolLib Parse bossLib;\n",
                encoding="utf-8",
            )

            holmake = root / "prefix" / "hol4" / "bin" / "Holmake"
            holmake.parent.mkdir(parents=True)
            holmake.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env bash
                    set -euo pipefail
                    test ! -e .hol/make-deps/lastmaker
                    test -f Holmakefile
                    test -f helloScript.sml
                    printf '%s\n' "$PWD" > "$HOL4_TEST_BUILD_DIR"
                    """
                ),
                encoding="utf-8",
            )
            holmake.chmod(0o755)

            build_dir_record = root / "build-dir"
            env = os.environ.copy()
            env.update(
                {
                    "HOL4_TEST_BUILD_DIR": str(build_dir_record),
                    "ITPEVAL_PREFIX": str(root / "prefix"),
                    "ITPEVAL_TASK_DIR": str(task_dir),
                    "TMPDIR": str(root),
                }
            )
            check = (
                Path(__file__).resolve().parents[1]
                / "provers"
                / "hol4"
                / "check.sh"
            )
            result = subprocess.run(
                ["/bin/bash", str(check)],
                cwd=task_dir,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                text=True,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                stale_cache.read_text(encoding="utf-8"),
                "/stale/Holmake\n",
            )
            self.assertNotEqual(
                Path(build_dir_record.read_text(encoding="utf-8").strip()),
                task_dir,
            )


if __name__ == "__main__":
    unittest.main()
