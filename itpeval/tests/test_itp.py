from __future__ import annotations

import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

from itpeval.itp import HOL4_TARGET_MARKER, _prepare_task_dir, run_itp


SUCCESS_OUTPUT = """\
No errors were found.  However, proofs were not checked.
All proofs in the database were verified in 0.00 s.
"""


class TaskPreparationTests(unittest.TestCase):
    def test_isabelle_theory_extraction_ignores_nested_comments(self) -> None:
        code = """\
(* theory Commented
   (* theory Nested *)
*)
theory Actual
  imports Main
begin
end
"""
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            _prepare_task_dir(
                prover="isabelle",
                code=code,
                mode="raw",
                task_dir=task_dir,
            )
            root = (task_dir / "ROOT").read_text(encoding="utf-8")
            self.assertTrue((task_dir / "Actual.thy").is_file())
            self.assertFalse((task_dir / "Commented.thy").exists())
        self.assertIn("ITPEval_Actual", root)
        self.assertIn("    Actual", root)

    def test_isabelle_preparation_handles_minif2f_placeholder_and_session(self) -> None:
        code = """\
theory Actual
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem example: True
  by sorry

end
"""
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            _prepare_task_dir(
                prover="isabelle",
                code=code,
                mode="raw",
                task_dir=task_dir,
            )
            root = (task_dir / "ROOT").read_text(encoding="utf-8")
            theory = (task_dir / "Actual.thy").read_text(encoding="utf-8")

        self.assertIn('  sessions\n    "HOL-Computational_Algebra"', root)
        self.assertIn("\n  sorry\n", theory)
        self.assertNotIn("\n  by sorry\n", theory)

    def test_metamath_raw_preparation_uses_hello_database(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            _prepare_task_dir(
                prover="metamath",
                code="$c token $.",
                mode="raw",
                task_dir=task_dir,
            )
            self.assertEqual(
                (task_dir / "hello.mm").read_text(encoding="utf-8"),
                "$c token $.\n",
            )

    def test_acl2_raw_preparation_uses_hello_script(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            _prepare_task_dir(
                prover="acl2",
                code='(in-package "ACL2")\n:q',
                mode="raw",
                task_dir=task_dir,
            )
            self.assertEqual(
                (task_dir / "hello.lsp").read_text(encoding="utf-8"),
                '(in-package "ACL2")\n:q\n',
            )

    def test_agda_raw_preparation_matches_module_filename(self) -> None:
        code = "module AgentTarget where\n\nStatement : Set\nStatement = Set\n"
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            selected = _prepare_task_dir(
                prover="agda",
                code=code,
                mode="raw",
                task_dir=task_dir,
            )
            self.assertEqual(selected, Path("AgentTarget.agda"))
            self.assertEqual(
                (task_dir / "AgentTarget.agda").read_text(),
                code,
            )

    def test_pvs_raw_preparation_matches_theory_filename(self) -> None:
        code = (
            "AgentTarget: THEORY\n"
            "BEGIN\n"
            "statement: bool = TRUE\n"
            "END AgentTarget\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            selected = _prepare_task_dir(
                prover="pvs",
                code=code,
                mode="raw",
                task_dir=task_dir,
            )
            self.assertEqual(selected, Path("AgentTarget.pvs"))
            self.assertEqual(
                (task_dir / "AgentTarget.pvs").read_text(),
                code,
            )

    def test_hol4_raw_preparation_adds_fixed_wrapper(self) -> None:
        code = "val statement = ``T``;\n"
        with tempfile.TemporaryDirectory() as tmp:
            task_dir = Path(tmp)
            selected = _prepare_task_dir(
                prover="hol4",
                code=code,
                mode="raw",
                task_dir=task_dir,
            )
            self.assertEqual(selected, Path("AgentTarget.sml"))
            self.assertEqual(
                {path.name for path in task_dir.iterdir()},
                {"AgentTarget.sml", "Holmakefile", "helloScript.sml"},
            )
            self.assertIn(
                HOL4_TARGET_MARKER,
                (task_dir / "helloScript.sml").read_text(),
            )

    def test_task_file_requires_task_directory(self) -> None:
        with self.assertRaisesRegex(
            ValueError,
            "--task-file requires --task-dir",
        ):
            run_itp(
                prover="metamath",
                code="$c token $.",
                task_file=Path("selected.mm"),
            )


class MetamathCheckTests(unittest.TestCase):
    def _run_check(
        self,
        *,
        files: tuple[str, ...],
        task_file: str | None = None,
        output: str = SUCCESS_OUTPUT,
        returncode: int = 0,
        outside_file: bool = False,
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_dir = root / "task"
            task_dir.mkdir()
            for filename in files:
                (task_dir / filename).write_text("$c token $.\n")
            if outside_file:
                (root / "outside.mm").write_text("$c token $.\n")

            metamath = root / "prefix" / "metamath" / "bin" / "metamath"
            metamath.parent.mkdir(parents=True)
            metamath.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env bash
                    printf '%s\n' "$*"
                    printf '%s\n' "${FAKE_METAMATH_OUTPUT}"
                    exit "${FAKE_METAMATH_RC}"
                    """
                ),
                encoding="utf-8",
            )
            metamath.chmod(0o755)

            env = os.environ.copy()
            env.update(
                {
                    "ITPEVAL_PREFIX": str(root / "prefix"),
                    "ITPEVAL_TASK_DIR": str(task_dir),
                    "FAKE_METAMATH_OUTPUT": output,
                    "FAKE_METAMATH_RC": str(returncode),
                }
            )
            if task_file is None:
                env.pop("ITPEVAL_TASK_FILE", None)
            else:
                env["ITPEVAL_TASK_FILE"] = task_file

            return subprocess.run(
                [
                    "/bin/bash",
                    str(
                        Path(__file__).resolve().parents[1]
                        / "provers"
                        / "metamath"
                        / "check.sh"
                    ),
                ],
                cwd=task_dir,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                text=True,
            )

    def test_selected_file_is_verified(self) -> None:
        result = self._run_check(
            files=("ignored.mm", "selected.mm"),
            task_file="selected.mm",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("read selected.mm verify proof * exit", result.stdout)

    def test_parser_error_is_rejected_even_with_zero_exit(self) -> None:
        result = self._run_check(
            files=("hello.mm",),
            output="?Error on line 1\n" + SUCCESS_OUTPUT,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("parser or verifier error", result.stderr)

    def test_missing_success_marker_is_rejected(self) -> None:
        result = self._run_check(
            files=("hello.mm",),
            output="No errors were found.",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("proof-verification marker", result.stderr)

    def test_multiple_file_fallback_is_rejected(self) -> None:
        result = self._run_check(files=("first.mm", "second.mm"))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("expected exactly one root .mm file", result.stderr)

    def test_outside_task_directory_is_rejected(self) -> None:
        result = self._run_check(
            files=("inside.mm",),
            task_file="../outside.mm",
            outside_file=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must resolve inside task directory", result.stderr)


class Acl2CheckTests(unittest.TestCase):
    def _run_check(
        self,
        *,
        files: dict[str, str],
        task_file: str | None = None,
        output: str = ":ITPEVAL-STATEMENT-CHECKED",
        returncode: int = 0,
        outside_file: bool = False,
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_dir = root / "task"
            task_dir.mkdir()
            for filename, content in files.items():
                (task_dir / filename).write_text(content, encoding="utf-8")
            if outside_file:
                (root / "outside.lsp").write_text(":q\n", encoding="utf-8")

            acl2 = root / "prefix" / "acl2" / "bin" / "acl2"
            acl2.parent.mkdir(parents=True)
            acl2.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env bash
                    input="$(cat)"
                    printf '%s\n' "${input}"
                    printf '%s\n' "${FAKE_ACL2_OUTPUT}"
                    exit "${FAKE_ACL2_RC}"
                    """
                ),
                encoding="utf-8",
            )
            acl2.chmod(0o755)

            env = os.environ.copy()
            env.update(
                {
                    "ITPEVAL_PREFIX": str(root / "prefix"),
                    "ITPEVAL_TASK_DIR": str(task_dir),
                    "FAKE_ACL2_OUTPUT": output,
                    "FAKE_ACL2_RC": str(returncode),
                }
            )
            if task_file is None:
                env.pop("ITPEVAL_TASK_FILE", None)
            else:
                env["ITPEVAL_TASK_FILE"] = task_file

            return subprocess.run(
                [
                    "/bin/bash",
                    str(
                        Path(__file__).resolve().parents[1]
                        / "provers"
                        / "acl2"
                        / "check.sh"
                    ),
                ],
                cwd=task_dir,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                text=True,
            )

    def test_selected_statement_file_is_checked(self) -> None:
        statement = (
            '(in-package "ACL2")\n'
            "(defun selected-statement (x) (equal x x))\n"
            "(value-triple :itpeval-statement-checked)\n"
            ":q\n"
        )
        result = self._run_check(
            files={"ignored.lsp": ":q\n", "selected.lsp": statement},
            task_file="selected.lsp",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("selected-statement", result.stdout)

    def test_acl2_error_is_rejected_even_with_zero_exit(self) -> None:
        result = self._run_check(
            files={
                "hello.lsp": (
                    "(defun problem-statement (x) (equal x x))\n"
                    "(value-triple :itpeval-statement-checked)\n"
                )
            },
            output="ACL2 Error in ( DEFUN PROBLEM-STATEMENT ...)\n"
            ":ITPEVAL-STATEMENT-CHECKED",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("reported a rejected event", result.stderr)

    def test_statement_mode_rejects_proof_events(self) -> None:
        result = self._run_check(
            files={
                "hello.lsp": (
                    "(defun problem-statement (x) (equal x x))\n"
                    "(defthm smuggled-proof (equal x x))\n"
                    "(value-triple :itpeval-statement-checked)\n"
                )
            }
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("theorem event", result.stderr)

    def test_statement_mode_allows_system_books_and_defun_sk(self) -> None:
        result = self._run_check(
            files={
                "hello.lsp": (
                    '(include-book "arithmetic/top" :dir :system)\n'
                    "(defun-sk has-square-root (x)\n"
                    "  (exists (y) (equal (* y y) x)))\n"
                    "(value-triple :itpeval-statement-checked)\n"
                    ":q\n"
                )
            }
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("defun-sk has-square-root", result.stdout)

    def test_statement_mode_rejects_local_books(self) -> None:
        result = self._run_check(
            files={
                "hello.lsp": (
                    '(include-book "local-book")\n'
                    "(defun problem-statement (x) (equal x x))\n"
                    "(value-triple :itpeval-statement-checked)\n"
                    ":q\n"
                )
            }
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("pinned `:dir :system` tree", result.stderr)

    def test_statement_mode_requires_sentinel_output(self) -> None:
        result = self._run_check(
            files={
                "hello.lsp": (
                    "(defun problem-statement (x) (equal x x))\n"
                    "(value-triple :itpeval-statement-checked)\n"
                )
            },
            output="Completed",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("statement-check sentinel", result.stderr)

    def test_existing_proof_smoke_mode_still_passes(self) -> None:
        result = self._run_check(
            files={"hello.lsp": "(defthm hello-plus (equal (+ 2 2) 4))\n:q\n"},
            output="Q.E.D.",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("proof script completed successfully", result.stderr)

    def test_multiple_file_fallback_is_rejected(self) -> None:
        result = self._run_check(
            files={"first.lsp": ":q\n", "second.lsp": ":q\n"}
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("expected exactly one root .lsp file", result.stderr)

    def test_outside_task_directory_is_rejected(self) -> None:
        result = self._run_check(
            files={"inside.lsp": ":q\n"},
            task_file="../outside.lsp",
            outside_file=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must resolve inside task directory", result.stderr)


if __name__ == "__main__":
    unittest.main()
