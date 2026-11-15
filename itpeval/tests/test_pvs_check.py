from __future__ import annotations

import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

from itpeval.validation import validate_statement_only


class PvsCheckTests(unittest.TestCase):
    def test_native_formula_declaration_is_a_valid_statement(self) -> None:
        validate_statement_only(
            "pvs",
            textwrap.dedent(
                """\
                % Statement-only formalization of a regression target.
                regression: THEORY
                BEGIN
                  target: FORMULA 1 = 1
                END regression
                """
            ),
        )

    def test_statement_rejects_inline_proof_script(self) -> None:
        with self.assertRaisesRegex(ValueError, "inline proof"):
            validate_statement_only(
                "pvs",
                textwrap.dedent(
                    """\
                    % Statement-only formalization of a regression target.
                    regression: THEORY
                    BEGIN
                      target: LEMMA 1 = 1
                    %|- (grind)
                    END regression
                    """
                ),
            )

    def test_statement_uses_typecheck_only_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_dir = root / "task"
            task_dir.mkdir()
            statement = task_dir / "native.pvs"
            statement.write_text(
                "% Statement-only formalization of a regression target.\n"
                "native: THEORY\nBEGIN\n  target: FORMULA 1 = 1\nEND native\n",
                encoding="utf-8",
            )

            proveit = root / "prefix" / "pvs" / "bin" / "proveit"
            proveit.parent.mkdir(parents=True)
            proveit.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env bash
                    set -euo pipefail
                    test "$1" = "-T"
                    test -f "$2"
                    """
                ),
                encoding="utf-8",
            )
            proveit.chmod(0o755)

            env = os.environ.copy()
            env.update(
                {
                    "ITPEVAL_PREFIX": str(root / "prefix"),
                    "ITPEVAL_TASK_DIR": str(task_dir),
                    "TMPDIR": str(root),
                }
            )
            check = (
                Path(__file__).resolve().parents[1]
                / "provers"
                / "pvs"
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

    def test_check_uses_clean_copy_of_task(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_dir = root / "task"
            task_dir.mkdir()
            statement = task_dir / "hello.pvs"
            statement.write_text(
                "hello: THEORY\nBEGIN\n  answer: THEOREM 1 = 1\nEND hello\n",
                encoding="utf-8",
            )
            context = task_dir / ".pvscontext"
            context.write_text("stale context\n", encoding="utf-8")
            summary = task_dir / "hello.summary"
            summary.write_text("stale summary\n", encoding="utf-8")
            cache = task_dir / "pvsbin" / "hello.bin"
            cache.parent.mkdir()
            cache.write_text("stale cache\n", encoding="utf-8")

            proveit = root / "prefix" / "pvs" / "bin" / "proveit"
            proveit.parent.mkdir(parents=True)
            proveit.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env bash
                    set -euo pipefail
                    test ! -e .pvscontext
                    test ! -e hello.summary
                    test ! -e pvsbin
                    test -f "$1"
                    printf '%s\n' "$PWD" > "$PVS_TEST_BUILD_DIR"
                    touch .pvscontext hello.summary
                    mkdir -p pvsbin
                    touch pvsbin/hello.bin
                    """
                ),
                encoding="utf-8",
            )
            proveit.chmod(0o755)

            build_dir_record = root / "build-dir"
            env = os.environ.copy()
            env.update(
                {
                    "ITPEVAL_PREFIX": str(root / "prefix"),
                    "ITPEVAL_TASK_DIR": str(task_dir),
                    "PVS_TEST_BUILD_DIR": str(build_dir_record),
                    "TMPDIR": str(root),
                }
            )
            check = (
                Path(__file__).resolve().parents[1]
                / "provers"
                / "pvs"
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
                context.read_text(encoding="utf-8"),
                "stale context\n",
            )
            self.assertEqual(
                summary.read_text(encoding="utf-8"),
                "stale summary\n",
            )
            self.assertEqual(
                cache.read_text(encoding="utf-8"),
                "stale cache\n",
            )
            self.assertNotEqual(
                Path(build_dir_record.read_text(encoding="utf-8").strip()),
                task_dir,
            )


if __name__ == "__main__":
    unittest.main()
