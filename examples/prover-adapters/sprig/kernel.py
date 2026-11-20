"""Sprig's certificate checker for classical propositional resolution."""
from __future__ import annotations

import re

Clause = frozenset[str]
ATOM = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def negate(literal: str) -> str:
    return literal[1:] if literal.startswith("~") else "~" + literal


def clause(value: object) -> Clause:
    if not isinstance(value, list):
        raise ValueError("a clause must be a list of literals")
    for literal in value:
        if not isinstance(literal, str) or not ATOM.fullmatch(literal.removeprefix("~")):
            raise ValueError(f"invalid literal {literal!r}")
    return frozenset(value)


def clause_statement(value: object) -> str:
    clause(value)
    return " | ".join(value) or "False"


def initial_clauses(problem: object) -> list[Clause]:
    if not isinstance(problem, dict) or set(problem) != {"premises", "goal"}:
        raise ValueError("a problem needs premises and a goal")
    if not isinstance(problem["premises"], list):
        raise ValueError("premises must be a list of clauses")
    premises = [clause(row) for row in problem["premises"]]
    # Refute the premises plus the negation of the goal disjunction.
    return premises + [frozenset([negate(lit)]) for lit in sorted(clause(problem["goal"]))]


def check(problem: object, certificate: object) -> None:
    """Replay a certificate against the caller's problem. Raise ValueError on rejection."""
    clauses = initial_clauses(problem)
    if not isinstance(certificate, dict) or set(certificate) != {"steps", "conclusion"}:
        raise ValueError("a certificate needs steps and a conclusion index")
    if not isinstance(certificate["steps"], list):
        raise ValueError("steps must be a list")
    for step in certificate["steps"]:
        index = len(clauses)
        if not isinstance(step, list) or len(step) != 3:
            raise ValueError(f"step {index}: expected [positive_parent, negative_parent, atom]")
        left, right, pivot = step
        if any(type(i) is not int or not 0 <= i < index for i in (left, right)):
            raise ValueError(f"step {index}: parents must refer to earlier clauses")
        if not isinstance(pivot, str) or not ATOM.fullmatch(pivot):
            raise ValueError(f"step {index}: expected a positive pivot atom")
        if pivot not in clauses[left] or "~" + pivot not in clauses[right]:
            raise ValueError(f"step {index}: parents do not contain opposite signs of {pivot}")
        clauses.append((clauses[left] - {pivot}) | (clauses[right] - {"~" + pivot}))
    end = certificate["conclusion"]
    if type(end) is not int or not 0 <= end < len(clauses) or clauses[end]:
        raise ValueError("the conclusion must identify the empty clause")


def check_assumptions(problem: dict, certificate: dict) -> tuple[str, ...]:
    """Check the proof and report which problem premises its conclusion uses."""
    check(problem, certificate)
    premises = len(problem["premises"])
    initial = len(initial_clauses(problem))
    pending, seen = [certificate["conclusion"]], set()
    while pending:
        index = pending.pop()
        if index in seen:
            continue
        seen.add(index)
        if index >= initial:
            pending.extend(certificate["steps"][index - initial][:2])
    return tuple(f"premise_{index}" for index in sorted(seen) if index < premises)
