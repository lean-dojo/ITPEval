"""Recognize compositions of task-authorized, indivisible prover commands."""
import re


# These tokens are never proof commands in this profile, even when accidentally
# included in the editable vocabulary of an otherwise trusted manifest.
_ADMISSION = re.compile(r"\b(sorry|admit|admitted|oops|cheat|skip-proofs|defaxiom|new_axiom|"
                        r"mk_oracle_thm|mk_thm|postulate|axiomatization)\b", re.IGNORECASE)


def _hol_tactic_tree(candidate, atoms, separator):
    """Accept the canonical THENL rendering built from authorized HOL tactics."""
    vocabulary = sorted((atom for atom in set(atoms) if atom), key=len, reverse=True)
    branches = ") THENL ["
    steps = 0

    def consume_atom(start, endings):
        for atom in vocabulary:
            end = start + len(atom)
            if candidate.startswith(atom, start) and any(
                    candidate.startswith(ending, end) if ending else end == len(candidate)
                    for ending in endings):
                return end
        return None

    def consume_tree(start, endings):
        nonlocal steps
        steps += 1
        if steps > 256:
            return None
        leaf = consume_atom(start, endings)
        if leaf is not None:
            return leaf
        if not candidate.startswith("((", start):
            return None
        head = consume_atom(start + 2, (branches,))
        if head is None:
            return None
        position = head + len(branches)
        while True:
            end = consume_tree(position, (separator, "])"))
            if end is None or candidate.startswith("])", end):
                return None if end is None else end + 2
            if not candidate.startswith(separator, end):
                return None
            position = end + len(separator)

    return consume_tree(0, ("",)) == len(candidate)


def permitted(prover: str, candidate: str, literals: tuple[str, ...], atoms: tuple[str, ...]) -> bool:
    if not candidate or len(candidate.encode("utf-8")) > 65536:
        return False
    if (_ADMISSION.search(candidate)
            or (prover == "metamath" and any(ch in candidate for ch in "$?"))
            or (prover == "mizar" and "::$" in candidate)
            or (prover == "agda" and ("?" in candidate or "{!" in candidate or "{-#" in candidate))):
        return False
    if candidate in literals:
        return True
    if not atoms:
        return False
    if prover == "lean4":
        parts = candidate.split(" <;> ")
    elif prover in ("hol4", "hol-light"):
        if candidate.startswith("((") and " THENL [" in candidate:
            if _hol_tactic_tree(candidate, atoms, ", " if prover == "hol4" else "; "):
                return True
        parts = candidate.split(" THEN ")
    elif prover == "rocq":
        commands = candidate.split("\n")
        if any(not command.endswith(".") for command in commands):
            return False
        parts = [part for command in commands for part in command[:-1].split("; ")]
    elif prover == "metamath":
        parts = candidate.split()
    elif prover == "mizar":
        parts = [line.strip() for line in candidate.splitlines()]
    elif prover == "pvs" and candidate.startswith("(then ") and candidate.endswith(")"):
        parts = re.findall(r"\([^()]+\)", candidate)
        if "(then " + " ".join(parts) + ")" != candidate:
            return False
    elif prover == "acl2":
        proof = re.fullmatch(r":instructions \((:[a-z]+(?: :[a-z]+)*)\)", candidate)
        if proof is None:
            return False
        parts = proof[1].split()
    else:
        return False
    return 0 < len(parts) <= 256 and all(part in atoms for part in parts)
