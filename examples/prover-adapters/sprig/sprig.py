"""Sprig: a small proof-producing propositional resolution prover."""
from __future__ import annotations

import argparse
import heapq
import json
import sys
from collections import defaultdict
from pathlib import Path

from kernel import check, initial_clauses, negate


class SearchLimit(Exception):
    """The next inference would exceed the requested search budget."""


def prove(problem: object, max_inferences: int = 10_000) -> dict | None:
    """Find a resolution refutation, return None at saturation, or raise SearchLimit."""
    if max_inferences < 0:
        raise ValueError("max_inferences must be nonnegative")
    clauses = initial_clauses(problem)
    steps = []
    known = set()
    queue = []
    active = defaultdict(list)
    for index, row in enumerate(clauses):
        if not row:
            return {"steps": [], "conclusion": index}
        if row not in known and not any(negate(lit) in row for lit in row):
            heapq.heappush(queue, (len(row), index))
            known.add(row)

    attempts = 0
    while queue:
        _, current = heapq.heappop(queue)
        row = clauses[current]
        for literal in sorted(row):
            opposite = negate(literal)
            for other in active[opposite]:
                if attempts == max_inferences:
                    raise SearchLimit
                attempts += 1
                derived = (row - {literal}) | (clauses[other] - {opposite})
                if derived in known or any(negate(lit) in derived for lit in derived):
                    continue
                index = len(clauses)
                if literal.startswith("~"):
                    steps.append([other, current, opposite])
                else:
                    steps.append([current, other, literal])
                if not derived:
                    return {"steps": steps, "conclusion": index}
                known.add(derived)
                clauses.append(derived)
                heapq.heappush(queue, (len(derived), index))
        # Index only after all inferences so the two parents are distinct.
        for literal in row:
            active[literal].append(current)
    return None


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version="Sprig 1 (propositional resolution)")
    commands = parser.add_subparsers(dest="command", required=True)
    search = commands.add_parser("prove", help="write a proof certificate as JSON to stdout")
    search.add_argument("problem", type=Path)
    search.add_argument("--max-inferences", type=int, default=10_000)
    replay = commands.add_parser("check", help="replay a certificate against a given problem")
    replay.add_argument("problem", type=Path)
    replay.add_argument("certificate", type=Path)
    args = parser.parse_args()
    try:
        problem = read_json(args.problem)
        if args.command == "check":
            check(problem, read_json(args.certificate))
            print("accepted")
            return 0
        certificate = prove(problem, args.max_inferences)
        if certificate is None:
            print("not entailed: saturated the clauses without a contradiction", file=sys.stderr)
            return 1
        check(problem, certificate)
        print(json.dumps(certificate))
        return 0
    except SearchLimit:
        print("unknown: inference budget exhausted", file=sys.stderr)
        return 2
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
