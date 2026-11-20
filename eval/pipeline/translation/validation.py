"""Authorization of indexed source-signature constants in the historical translation benchmark."""
import argparse
import json
import re
from functools import lru_cache
from pathlib import Path

from itpeval import validation

_LEAN_SOURCE_SIGNATURE_MARKER = re.compile(
    r"^\s*--\s*itpeval-source-signature:\s*"
    r"logipedia:(?P<source>[A-Za-z_][A-Za-z0-9_.]*)\s+"
    r"as\s+(?P<local>[A-Za-z_][A-Za-z0-9_]*)\s*$"
)
_LEAN_SOURCE_SIGNATURE_AXIOM = re.compile(
    r"^(?P<indent>\s*)axiom\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*:"
)


@lru_cache(maxsize=1)
def _logipedia_constant_ids() -> frozenset[str]:
    from eval.datasets import logipedia_index
    index_path = logipedia_index()
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
    if not any(_LEAN_SOURCE_SIGNATURE_MARKER.match(line) for line in lines):
        return text
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



def validate_statement_only(prover: str, text: str) -> None:
    if prover == "lean4":
        text = _mask_authorized_lean_source_signatures(text)
    validation.validate_statement_only(prover, text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--prover", required=True)
    parser.add_argument("--file", type=Path, required=True)
    args = parser.parse_args()
    try:
        validate_statement_only(args.prover, args.file.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        parser.exit(1, f"[ITPEval] ERROR: {exc}\n")
