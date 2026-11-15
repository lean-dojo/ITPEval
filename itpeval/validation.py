from __future__ import annotations

import argparse
import json
import re
from functools import lru_cache
from pathlib import Path


_ADMISSION = re.compile(
    r"\b(?:sorry|admit|admitted|oops|cheat)\b",
    re.IGNORECASE,
)

_ACL2_INCLUDE_BOOK = re.compile(
    r"(?is)\(\s*(?:acl2::)?include-book\b(?P<body>[^()]*)\)"
)
_ACL2_INCLUDE_BOOK_HEAD = re.compile(
    r"(?i)\(\s*(?:acl2::)?include-book\b"
)
_ACL2_PROVERS = frozenset({"acl2", "acl2r"})
_LEAN_SOURCE_SIGNATURE_MARKER = re.compile(
    r"^\s*--\s*itpeval-source-signature:\s*"
    r"logipedia:(?P<source>[A-Za-z_][A-Za-z0-9_.]*)\s+"
    r"as\s+(?P<local>[A-Za-z_][A-Za-z0-9_]*)\s*$"
)
_LEAN_SOURCE_SIGNATURE_AXIOM = re.compile(
    r"^(?P<indent>\s*)axiom\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*:"
)


_AXIOM_PATTERNS: dict[str, tuple[str, str, int]] = {
    "lean4": (
        r"(?m)^\s*(?:@\[[^\]\r\n]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:axiom|constant)\b",
        "Lean statement declares an axiom or unimplemented constant",
        0,
    ),
    "rocq": (
        r"(?im)^\s*(?:#\[[^\]\r\n]*\]\s*)*"
        r"(?:Axiom|Axioms|Conjecture)\b",
        "Rocq statement declares an axiom or conjecture",
        0,
    ),
    "isabelle": (
        r"(?im)^\s*(?:axiomatization|axioms|oracle|ML|ML_file|"
        r"setup|local_setup)\b",
        "Isabelle statement declares an axiom, oracle, or unchecked ML hook",
        0,
    ),
    "hol-light": (
        r"\b(?:new_axiom|mk_thm)\b",
        "HOL Light statement uses an axiom or raw theorem constructor",
        0,
    ),
    "hol4": (
        r"\b(?:new_axiom|mk_thm|mk_oracle_thm)\b",
        "HOL4 statement uses an axiom, oracle, or raw theorem constructor",
        0,
    ),
    "agda": (
        r"(?m)^\s*(?:postulate|primitive)\b|\{!!\}|\?(?![\w'-])|"
        r"\{\-\#\s*(?:TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|"
        r"NO_UNIVERSE_CHECK|NO_COVERAGE_CHECK|POLARITY|NON_COVERING)\b",
        "Agda statement contains a postulate, hole, or unsafe pragma",
        re.IGNORECASE,
    ),
    "pvs": (
        r"(?im):\s*(?:AXIOM|POSTULATE|CONJECTURE)\b",
        "PVS statement contains an unproved declaration",
        0,
    ),
}


@lru_cache(maxsize=1)
def _logipedia_constant_ids() -> frozenset[str]:
    index_path = (
        Path(__file__).resolve().parents[1]
        / "data"
        / "logipedia"
        / "data"
        / "index.json"
    )
    try:
        index = json.loads(index_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError(
            f"cannot validate Logipedia source signatures: {exc}"
        ) from exc
    return frozenset(
        entry_id
        for entry_id, entry in index.get("entries", {}).items()
        if entry.get("kind") == "constant"
    )


def _mask_authorized_lean_source_signatures(text: str) -> str:
    lines = text.splitlines(keepends=True)
    constants = _logipedia_constant_ids()
    for index, line in enumerate(lines):
        marker = _LEAN_SOURCE_SIGNATURE_MARKER.match(
            line.removesuffix("\n").removesuffix("\r")
        )
        if marker is None:
            continue
        source_id = marker.group("source")
        local_name = marker.group("local")
        if source_id not in constants:
            raise ValueError(
                "Lean source-signature marker does not reference an indexed "
                f"Logipedia constant: {source_id!r}"
            )

        declaration_index = index + 1
        while (
            declaration_index < len(lines)
            and not lines[declaration_index].strip()
        ):
            declaration_index += 1
        if declaration_index >= len(lines):
            raise ValueError(
                "Lean source-signature marker is missing its declaration"
            )
        declaration = _LEAN_SOURCE_SIGNATURE_AXIOM.match(
            lines[declaration_index]
        )
        if declaration is None or declaration.group("name") != local_name:
            raise ValueError(
                "Lean source-signature marker must be followed by "
                f"`axiom {local_name} : ...`"
            )

        axiom_start = declaration.start("name") - len("axiom ")
        axiom_end = axiom_start + len("axiom")
        declaration_line = lines[declaration_index]
        lines[declaration_index] = (
            declaration_line[:axiom_start]
            + " " * len("axiom")
            + declaration_line[axiom_end:]
        )
    return "".join(lines)


def _strip_nested(
    text: str,
    *,
    opener: str,
    closer: str,
) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if text.startswith(opener, index):
            depth += 1
            output.extend(" " * len(opener))
            index += len(opener)
        elif depth and text.startswith(closer, index):
            depth -= 1
            output.extend(" " * len(closer))
            index += len(closer)
        else:
            char = text[index]
            output.append(char if depth == 0 or char == "\n" else " ")
            index += 1
    return "".join(output)


def without_prover_comments(text: str, prover: str | None) -> str:
    if prover == "lean4":
        text = _strip_nested(text, opener="/-", closer="-/")
        return re.sub(r"(?m)--.*$", "", text)
    if prover == "agda":
        text = _strip_nested(text, opener="{-", closer="-}")
        return re.sub(r"(?m)--.*$", "", text)
    if prover in {"rocq", "isabelle", "hol-light", "hol4"}:
        return _strip_nested(text, opener="(*", closer="*)")
    if prover in _ACL2_PROVERS:
        text = _strip_nested(text, opener="#|", closer="|#")
        return re.sub(r"(?m);.*$", "", text)
    if prover == "metamath":
        return _strip_nested(text, opener="$(", closer="$)")
    if prover == "mizar":
        return re.sub(r"(?m)::.*$", "", text)
    if prover == "pvs":
        return re.sub(r"(?m)%.*$", "", text)
    return text


def _require(pattern: str, text: str, message: str, *, flags: int = 0) -> None:
    if re.search(pattern, text, flags) is None:
        raise ValueError(message)


def _reject(pattern: str, text: str, message: str, *, flags: int = 0) -> None:
    match = re.search(pattern, text, flags)
    if match is not None:
        raise ValueError(f"{message}: {match.group(0)!r}")


def _validate_acl2_book_imports(code: str) -> None:
    heads = list(_ACL2_INCLUDE_BOOK_HEAD.finditer(code))
    forms = list(_ACL2_INCLUDE_BOOK.finditer(code))
    if len(heads) != len(forms):
        raise ValueError(
            "ACL2 `include-book` must use a literal, non-nested event form"
        )

    for form in forms:
        body = form.group("body")
        path_match = re.match(r'\s*"(?P<path>[^"]+)"', body)
        if path_match is None:
            raise ValueError("ACL2 `include-book` path must be a string literal")
        book_path = Path(path_match.group("path"))
        if (
            book_path.is_absolute()
            or ".." in book_path.parts
            or "\\" in path_match.group("path")
        ):
            raise ValueError(
                "ACL2 `include-book` path must stay inside the system books tree"
            )
        if re.search(r"(?i)(?:^|\s):dir\s+:system\b", body) is None:
            raise ValueError(
                "ACL2 `include-book` must select the pinned `:dir :system` tree"
            )
        if re.search(
            r"(?i)(?:^|\s):(?:uncertified-okp|ttags)\b",
            body,
        ):
            raise ValueError(
                "ACL2 `include-book` cannot bypass certification or enable trust tags"
            )


def validate_no_axiom_smuggling(prover: str, text: str) -> None:
    """Reject source constructs that enlarge or bypass the trusted logic."""
    validation_text = text
    if prover == "lean4":
        validation_text = _mask_authorized_lean_source_signatures(text)
    code = without_prover_comments(validation_text, prover)
    if prover == "agda":
        _reject(
            r"\{\-\#\s*(?:TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|"
            r"NO_UNIVERSE_CHECK|NO_COVERAGE_CHECK|POLARITY|NON_COVERING)\b",
            text,
            "Agda statement contains an unsafe pragma",
            flags=re.IGNORECASE,
        )
        _reject(
            r"\{\-\#\s*OPTIONS\b[^#]*"
            r"--(?:allow-unsolved-metas|allow-incomplete-matches|"
            r"type-in-type|omega-in-omega|no-termination-check|"
            r"no-positivity-check|no-universe-check|no-coverage-check|"
            r"no-confluence-check|allow-exec|no-load-primitives|rewriting)\b",
            text,
            "Agda statement enables an unsafe compiler option",
            flags=re.IGNORECASE,
        )
    policy = _AXIOM_PATTERNS.get(prover)
    if policy is not None:
        pattern, message, flags = policy
        _reject(pattern, code, message, flags=flags)

    if prover in _ACL2_PROVERS:
        _validate_acl2_book_imports(code)
        _reject(
            r"(?i)\(\s*(?:acl2::)?(?:defaxiom|skip-proofs|encapsulate|"
            r"make-event|defmacro|progn!|certify-book|defttag|include-raw|"
            r"set-raw-mode|set-ld-skip-proofsp|defattach|thm|prove\$|ld)\b",
            code,
            "ACL2 statement contains a proof, trust, or axiom-admission event",
        )


def validate_statement_only(prover: str, text: str) -> None:
    if not text.strip():
        raise ValueError("target translation is empty")
    code = without_prover_comments(text, prover)
    validate_no_axiom_smuggling(prover, text)

    if prover == "hol-light":
        _reject(r"\bprove\b", code, "HOL Light statement calls a prover")
    elif prover in _ACL2_PROVERS:
        _require(
            r"(?i)\(\s*(?:acl2::)?defun(?:-sk)?\b",
            code,
            "ACL2 statement must define a predicate with `defun` or `defun-sk`",
        )
        _require(
            r"(?i):itpeval-statement-checked\b",
            code,
            "ACL2 statement is missing the ITPEval sentinel",
        )
        _reject(
            r"(?i)\(\s*(?:acl2::)?(?:defthm|defthmd)\b",
            code,
            "ACL2 statement contains a theorem event",
        )
    elif prover == "agda":
        _require(
            r"(?m)^\s*module\s+\S+\s+where\b",
            code,
            "Agda statement must be a complete module",
        )
    elif prover == "hol4":
        _reject(
            r"\b(?:prove|store_thm|new_theory|export_theory)\b",
            code,
            "HOL4 statement contains proof or wrapper commands",
        )
        _require(
            r"``.*``",
            code,
            "HOL4 statement must bind at least one quoted proposition",
            flags=re.DOTALL,
        )
    elif prover == "metamath":
        _reject(r"\$p\b", code, "Metamath statement must not contain `$p` proofs")
        _require(r"\$a\b", code, "Metamath statement must contain a `$a` assertion")
    elif prover == "mizar":
        _require(
            r"(?m)^\s*::\$P-\s*$",
            text,
            "Mizar statement is missing `::$P-`",
        )
        _require(
            r"(?m)^\s*::\$P\+\s*$",
            text,
            "Mizar statement is missing `::$P+`",
        )
    elif prover == "pvs":
        _reject(
            r"(?m)^\s*%\|-",
            text,
            "PVS statement contains an inline proof script",
        )
        _reject(
            r"(?im):\s*(?:LEMMA|THEOREM|COROLLARY|PROPOSITION|"
            r"CHALLENGE|CLAIM|FACT|LAW|OBLIGATION)\b",
            code,
            "PVS statement contains a proof-bearing declaration",
        )
        _require(
            r"(?im)^\s*[A-Za-z][A-Za-z0-9_?'-]*"
            r"(?:\s*\([^)]*\))?\s*:\s*"
            r"(?:bool\s*=|FORMULA\b)",
            code,
            "PVS statement must contain a Boolean definition or formula declaration",
        )


def validate_proof_no_escape(prover: str | None, text: str) -> None:
    if not text.strip():
        raise ValueError("target translation is empty")
    code = without_prover_comments(text, prover)
    if prover is not None:
        validate_no_axiom_smuggling(prover, text)
    admission = _ADMISSION.search(code)
    if admission:
        raise ValueError(
            f"forbidden admission token {admission.group(0)!r} "
            "in ungrounded proof translation"
        )

    if prover in _ACL2_PROVERS:
        _reject(
            r"(?i)\(\s*(?:acl2::)?(?:defaxiom|skip-proofs|encapsulate|"
            r"make-event)\b",
            code,
            "ACL2 proof contains an escape hatch",
        )
        _require(
            r"(?i)\(\s*(?:acl2::)?defthm[d]?\b",
            code,
            "ACL2 proof must contain a checked theorem event",
        )
    elif prover == "agda":
        _reject(
            r"\bpostulate\b|\{!!\}|\?",
            code,
            "Agda proof contains a postulate or hole",
        )
    elif prover == "hol4":
        _reject(
            r"\b(?:new_axiom|mk_thm|new_theory|export_theory)\b",
            code,
            "HOL4 proof contains an axiom or wrapper command",
        )
    elif prover == "metamath":
        _require(r"\$p\b", code, "Metamath proof must contain a `$p` assertion")
    elif prover == "mizar":
        _reject(
            r"(?m)^\s*::\$P-\s*$",
            text,
            "Mizar proof uses proof-suppression pragmas",
        )
        _require(
            r"\bproof\b.*\bend\s*;",
            code,
            "Mizar proof must contain a checked proof block",
            flags=re.IGNORECASE | re.DOTALL,
        )
    elif prover == "pvs":
        _reject(
            r"(?im):\s*(?:AXIOM|POSTULATE|CONJECTURE)\b",
            code,
            "PVS proof contains an unproved declaration",
        )
        _require(
            r"(?im):\s*(?:LEMMA|THEOREM)\b",
            code,
            "PVS proof must contain a LEMMA or THEOREM",
        )
        _require(
            r"(?m)^\s*%\|-",
            text,
            "PVS proof must contain an inline ProofLite script",
        )


def _main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate an ITPEval statement-only source file."
    )
    parser.add_argument("--prover", required=True)
    parser.add_argument("--file", required=True, type=Path)
    args = parser.parse_args()
    try:
        validate_statement_only(
            args.prover,
            args.file.read_text(encoding="utf-8"),
        )
    except (OSError, UnicodeError, ValueError) as exc:
        parser.exit(1, f"[ITPEval] ERROR: {exc}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
