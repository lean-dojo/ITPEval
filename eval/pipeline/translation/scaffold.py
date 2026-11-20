from __future__ import annotations

import re
from dataclasses import dataclass

from eval.pipeline.config import STATEMENT_FENCE_ALIASES
from eval.pipeline.translation.validation import validate_statement_only
from itpeval.validation import validate_proof_no_escape


class ScaffoldError(ValueError):
    """Raised when a target scaffold or model proof response is invalid."""


@dataclass(frozen=True)
class ProofHole:
    name: str
    start: int
    end: int
    replacement_prefix: str
    replacement_suffix: str
    indent: str


@dataclass(frozen=True)
class AssemblyResult:
    code: str
    hole_names: tuple[str, ...]
    admission_free: bool


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


_DECLARATION_PATTERNS = {
    "lean4": re.compile(
        r"\b(?:theorem|lemma|def|instance|example)\s+"
        r"([A-Za-z_][A-Za-z0-9_'.]*)"
    ),
    "rocq": re.compile(
        r"\b(?:Theorem|Lemma|Fact|Remark|Corollary|Proposition)\s+"
        r"([A-Za-z_][A-Za-z0-9_']*)"
    ),
    "isabelle": re.compile(
        r"\b(?:lemma|theorem|corollary|proposition|interpretation)\s+"
        r"([A-Za-z_][A-Za-z0-9_']*)"
    ),
}

_LEAN_HOLE = re.compile(r"\bby\s+sorry\b")
_ROCQ_HOLE = re.compile(r"\bProof\.\s*Admitted\.", re.DOTALL)
_ISABELLE_HOLE = re.compile(r"\bsorry\b")
_HOL_LIGHT_THEOREM = re.compile(
    r"(?ms)"
    r"(?P<prefix>^[ \t]*let[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
    r"[ \t]*=\s*)"
    r"(?P<term>`[^`]*`)"
    r"[ \t]*;;"
)

_BLOCK = re.compile(
    r"(?ms)^<<<PROOF[ \t]+(?P<name>[A-Za-z0-9_'.]+)>>>[ \t]*\n"
    r"(?P<proof>.*?)"
    r"^<<<END PROOF>>>[ \t]*(?:\n|$)"
)

_FORBIDDEN_PROOF_TOKENS = re.compile(
    r"\b(?:sorry|admit|admitted|oops|cheat|axiom|new_axiom)\b",
    re.IGNORECASE,
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


def _nearest_declaration_name(prover: str, scaffold: str, position: int) -> str:
    pattern = _DECLARATION_PATTERNS[prover]
    matches = list(pattern.finditer(scaffold, 0, position))
    return matches[-1].group(1) if matches else "obligation"


def _number_holes(holes: list[ProofHole]) -> list[ProofHole]:
    width = max(3, len(str(len(holes))))
    return [
        ProofHole(
            name=f"{index:0{width}d}_{hole.name}",
            start=hole.start,
            end=hole.end,
            replacement_prefix=hole.replacement_prefix,
            replacement_suffix=hole.replacement_suffix,
            indent=hole.indent,
        )
        for index, hole in enumerate(holes, 1)
    ]


def _proof_holes_for_admitted_scaffold(
    prover: str,
    scaffold: str,
    hole_pattern: re.Pattern[str],
) -> list[ProofHole]:
    holes: list[ProofHole] = []
    for match in hole_pattern.finditer(scaffold):
        name = _nearest_declaration_name(prover, scaffold, match.start())
        if prover == "lean4":
            prefix, suffix, indent = "by\n", "", "  "
        elif prover == "rocq":
            prefix, suffix, indent = "Proof.\n", "\nQed.", ""
        else:
            prefix, suffix, indent = "", "", ""
        holes.append(
            ProofHole(
                name=name,
                start=match.start(),
                end=match.end(),
                replacement_prefix=prefix,
                replacement_suffix=suffix,
                indent=indent,
            )
        )
    return holes


def extract_proof_holes(
    prover: str,
    scaffold: str,
    *,
    allow_empty: bool = False,
) -> list[ProofHole]:
    """Return the proof obligations encoded by a target statement scaffold."""
    if prover == "lean4":
        holes = _proof_holes_for_admitted_scaffold(
            prover, scaffold, _LEAN_HOLE
        )
    elif prover == "rocq":
        holes = _proof_holes_for_admitted_scaffold(
            prover, scaffold, _ROCQ_HOLE
        )
    elif prover == "isabelle":
        holes = _proof_holes_for_admitted_scaffold(
            prover, scaffold, _ISABELLE_HOLE
        )
    elif prover == "hol-light":
        holes = []
        for match in _HOL_LIGHT_THEOREM.finditer(scaffold):
            prefix = match.group("prefix")
            term = match.group("term")
            holes.append(
                ProofHole(
                    name=match.group("name"),
                    start=match.start(),
                    end=match.end(),
                    replacement_prefix=f"{prefix}prove\n  ({term},\n",
                    replacement_suffix=");;",
                    indent="   ",
                )
            )
    else:
        raise ScaffoldError(f"unsupported target prover: {prover}")

    if not holes and not allow_empty:
        raise ScaffoldError(f"no proof holes found in {prover} target scaffold")

    return _number_holes(holes)


def parse_proof_blocks(
    response: str,
    expected_names: list[str],
    *,
    prover: str | None = None,
) -> dict[str, str]:
    """Parse strict, named proof-fragment blocks from a model response."""
    fragments: dict[str, str] = {}
    cursor = 0
    for match in _BLOCK.finditer(response):
        if response[cursor:match.start()].strip():
            raise ScaffoldError("unexpected text outside proof-fragment blocks")
        name = match.group("name")
        proof = match.group("proof").strip()
        if name in fragments:
            raise ScaffoldError(f"duplicate proof block: {name}")
        if not proof:
            raise ScaffoldError(f"empty proof block: {name}")
        forbidden = _FORBIDDEN_PROOF_TOKENS.search(proof)
        if forbidden:
            raise ScaffoldError(
                f"forbidden proof token {forbidden.group(0)!r} in block {name}"
            )
        if prover == "rocq":
            terminator = re.search(
                r"\b(?:Proof|Qed|Defined|Abort)\.",
                proof,
                re.IGNORECASE,
            )
            if terminator:
                raise ScaffoldError(
                    f"forbidden Rocq proof terminator "
                    f"{terminator.group(0)!r} in block {name}"
                )
        if prover == "hol-light" and ";;" in proof:
            raise ScaffoldError(
                f"forbidden HOL Light top-level terminator in block {name}"
            )
        fragments[name] = proof
        cursor = match.end()

    if response[cursor:].strip():
        raise ScaffoldError("unexpected text outside proof-fragment blocks")

    expected = set(expected_names)
    actual = set(fragments)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing or extra:
        details = []
        if missing:
            details.append(f"missing: {', '.join(missing)}")
        if extra:
            details.append(f"extra: {', '.join(extra)}")
        raise ScaffoldError("proof block mismatch (" + "; ".join(details) + ")")
    return fragments


def _indent_fragment(fragment: str, indent: str) -> str:
    if not indent:
        return fragment
    return "\n".join(
        f"{indent}{line}" if line else ""
        for line in fragment.splitlines()
    )


def assemble_proof_response(
    prover: str,
    scaffold: str,
    response: str,
) -> AssemblyResult:
    """Insert model-provided proof fragments into the immutable scaffold."""
    holes = extract_proof_holes(prover, scaffold)
    names = [hole.name for hole in holes]
    fragments = parse_proof_blocks(response, names, prover=prover)

    code = scaffold
    for hole in reversed(holes):
        proof = _indent_fragment(fragments[hole.name], hole.indent)
        replacement = (
            hole.replacement_prefix + proof + hole.replacement_suffix
        )
        code = code[:hole.start] + replacement + code[hole.end:]

    if prover != "hol-light" and _FORBIDDEN_PROOF_TOKENS.search(code):
        # The target scaffolds may contain axioms as fixed context, so only
        # admission markers are meaningful at whole-file scope.
        remaining_admission = re.search(
            r"\b(?:sorry|admit|admitted|oops|cheat)\b",
            code,
            re.IGNORECASE,
        )
        if remaining_admission:
            raise ScaffoldError(
                f"assembled file still contains "
                f"{remaining_admission.group(0)!r}"
            )

    return AssemblyResult(
        code=code,
        hole_names=tuple(names),
        admission_free=True,
    )
