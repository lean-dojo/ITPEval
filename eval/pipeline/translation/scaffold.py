from __future__ import annotations

import re

from eval.pipeline.config import STATEMENT_FENCE_ALIASES
from eval.pipeline.translation.validation import validate_statement_only
from itpeval.validation import validate_proof_no_escape


class ScaffoldError(ValueError):
    """Raised when a model response has invalid output or formatting."""


_STATEMENT_FENCE = re.compile(
    r"(?ms)^[ \t]*```(?P<language>[^\n`]*)[ \t]*\n"
    r"(?P<code>.*?)"
    r"^[ \t]*```[ \t]*(?:\n|$)"
)


def extract_statement_response(prover: str, response: str) -> str:
    """Return raw statement code, unwrapping one compatible Markdown fence.

    Plain responses retain the historical raw-file behavior. Fenced responses
    must contain exactly one block for the requested prover (or one unlabelled
    block) so that explanatory text is never sent to the prover and ambiguous
    candidates are not selected silently.
    """
    if prover not in STATEMENT_FENCE_ALIASES:
        raise ScaffoldError(f"unsupported statement prover: {prover!r}")

    blocks = [
        (
            match.group("language").strip().lower(),
            match.group("code"),
        )
        for match in _STATEMENT_FENCE.finditer(response)
    ]
    if not blocks:
        if "```" in response:
            raise ScaffoldError("malformed Markdown code fence in statement response")
        return response

    aliases = STATEMENT_FENCE_ALIASES[prover]
    compatible = [code for language, code in blocks if language in aliases]
    if len(compatible) == 1:
        return compatible[0]
    if len(compatible) > 1:
        raise ScaffoldError(
            f"multiple {prover} Markdown code blocks in statement response"
        )

    unlabelled = [code for language, code in blocks if not language]
    if len(unlabelled) == 1 and len(blocks) == 1:
        return unlabelled[0]
    if len(blocks) == 1:
        language = blocks[0][0] or "unlabelled"
        raise ScaffoldError(
            f"statement response uses {language!r} Markdown fence for "
            f"{prover!r} target"
        )
    raise ScaffoldError(
        f"no unique {prover} Markdown code block in statement response"
    )


def validate_statement_output(prover: str, code: str) -> None:
    """Reject statement translations that smuggle proofs or admissions."""
    try:
        validate_statement_only(prover, code)
    except ValueError as exc:
        raise ScaffoldError(str(exc)) from exc


def validate_ungrounded_proof_output(
    code: str,
    *,
    prover: str | None = None,
) -> None:
    """Reject proof outputs that rely on an admission placeholder."""
    try:
        validate_proof_no_escape(prover, code)
    except ValueError as exc:
        raise ScaffoldError(str(exc)) from exc
