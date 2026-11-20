"""Qualify bounded Lean equivalence on extracted declarations from a pinned library."""

import argparse
import json
import os
from pathlib import Path

from itpeval.corpus.example import ENTRY, LIBRARY
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project
from itpeval.extraction import extract_project
from itpeval.learning.qualification import _record
from itpeval.semantics.lean import compare


def qualify(prefix, cache, output, report):
    prepared = prepare_project("lean4", LIBRARY / "lean4/library", prefix=prefix, cache=cache)
    entry = ENTRY["lean4"]
    bundle = extract_project(prepared, entry, cache / "extracted")
    declarations = {row["name"]: row["declaration_id"] for row in read_jsonl(bundle.path / "declarations.jsonl")}
    reference = declarations["first_successor"]
    results = {}
    for name in ("Counts.next_index_zero", "Counts.nextIndex"):
        results[name] = compare(prepared, entry, declarations[name], reference, cache=cache / "extracted").to_dict()
    positive, negative = results["Counts.next_index_zero"], results["Counts.nextIndex"]
    passed = (positive["status"] == "equivalence established" and positive["forward"] == positive["backward"] == "exact"
              and negative["status"] == "equivalence not established" and "proposition-valued" in negative["diagnostic"])
    path = output / "lean4/equivalence.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"entrypoint": entry, "extraction": bundle.path.name,
                                "right_name": "first_successor", "results": results}, indent=2) + "\n")
    _record(report, [{"prover": "lean4", "environment_id": prepared.environment_id,
                      "prover_build": prepared.spec.prover_build, "operation": "bounded_equivalence",
                      "status": "implemented/tested" if passed else "failed",
                      "evidence_path": os.path.relpath(path, report.parent)}])
    return passed


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("prefix", "cache", "output", "report"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    raise SystemExit(0 if qualify(args.prefix, args.cache, args.output, args.report) else 1)
