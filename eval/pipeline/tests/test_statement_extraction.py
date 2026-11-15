from __future__ import annotations

import unittest

from eval.pipeline.config import STATEMENT_FENCE_ALIASES
from eval.pipeline.translation.scaffold import (
    ScaffoldError,
    extract_statement_response,
    validate_statement_output,
)


class StatementExtractionTests(unittest.TestCase):
    def test_preserves_plain_statement_file(self) -> None:
        response = "theorem example : True := by sorry\n"
        self.assertEqual(
            extract_statement_response("lean4", response),
            response,
        )

    def test_extracts_target_tagged_block_from_explanation(self) -> None:
        response = (
            "### Lean 4 Statement\n\n"
            "```lean4\n"
            "theorem example : True := by sorry\n"
            "```\n\n"
            "This is the translation.\n"
        )
        self.assertEqual(
            extract_statement_response("lean4", response),
            "theorem example : True := by sorry\n",
        )

    def test_accepts_common_target_alias(self) -> None:
        response = "```coq\nTheorem example : True. Admitted.\n```\n"
        self.assertEqual(
            extract_statement_response("rocq", response),
            "Theorem example : True. Admitted.\n",
        )

    def test_accepts_every_configured_fence_alias(self) -> None:
        for prover, aliases in STATEMENT_FENCE_ALIASES.items():
            for alias in aliases:
                with self.subTest(prover=prover, alias=alias):
                    self.assertEqual(
                        extract_statement_response(
                            prover,
                            f"```{alias}\ntranslated\n```\n",
                        ),
                        "translated\n",
                    )

    def test_extracts_single_unlabelled_block(self) -> None:
        response = "Translation:\n```\ntheory Example imports Main begin\nend\n```\n"
        self.assertEqual(
            extract_statement_response("isabelle", response),
            "theory Example imports Main begin\nend\n",
        )

    def test_rejects_wrong_language_tag(self) -> None:
        with self.assertRaisesRegex(ScaffoldError, "uses 'lean4'.*'isabelle'"):
            extract_statement_response(
                "isabelle",
                "```lean4\ntheorem example : True := by sorry\n```\n",
            )

    def test_rejects_multiple_target_blocks(self) -> None:
        with self.assertRaisesRegex(ScaffoldError, "multiple lean4"):
            extract_statement_response(
                "lean4",
                "```lean4\nfirst\n```\n```lean\nsecond\n```\n",
            )

    def test_rejects_malformed_fence(self) -> None:
        with self.assertRaisesRegex(ScaffoldError, "malformed"):
            extract_statement_response(
                "rocq",
                "```coq\nTheorem example : True. Admitted.\n",
            )

    def test_validates_added_prover_statement_formats(self) -> None:
        fixtures = {
            "acl2": (
                '(in-package "ACL2")\n'
                "(defun statement (x) (equal x x))\n"
                "(value-triple :itpeval-statement-checked)\n:q\n"
            ),
            "agda": "module AgentTarget where\nStatement : Set\nStatement = Set\n",
            "hol4": "val statement = ``T``;\n",
            "metamath": "$c wff $.\nstatement $a wff $.\n",
            "mizar": "environ\nbegin\n::$P-\ntheorem 1 = 1\nproof\nend;\n::$P+\n",
            "pvs": (
                "AgentTarget: THEORY\nBEGIN\n"
                "statement: bool = TRUE\n"
                "END AgentTarget\n"
            ),
        }
        for prover, code in fixtures.items():
            with self.subTest(prover=prover):
                validate_statement_output(prover, code)

    def test_rejects_statement_proof_escape_hatches(self) -> None:
        with self.assertRaisesRegex(ScaffoldError, "proof"):
            validate_statement_output(
                "hol4",
                "val statement = prove (``T``, REWRITE_TAC []);\n",
            )
        with self.assertRaisesRegex(ScaffoldError, "proof"):
            validate_statement_output(
                "metamath",
                "$c wff $. statement $p wff $= ? $.\n",
            )


if __name__ == "__main__":
    unittest.main()
