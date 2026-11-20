"""Qualify Isa-REPL proof-state rollback in an isolated HOL process."""
import argparse
import json
from pathlib import Path

from itpeval.backends.isabelle.interaction import branch_trace
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.learning.qualification import _record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "integrations", "output", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    prepared = prepare_project("isabelle", curated_project("isabelle"), prefix=args.prefix,
                               cache=args.cache, toolchain_inputs={role: args.integrations / role
                               for role in ("isa_repl", "auto_sledgehammer")})
    task = build_task(prepared)
    trace = branch_trace(task, task.allowed_edits, prepared=prepared)
    before = trace["initial"][-1]
    branches = trace["branches"]
    closed = [bool(b["commands"] and not b["error"] and
                   not b["commands"][-1]["flags"][0]["has_goal"]) for b in branches]
    operations = {"inspect_goals": before["flags"][0]["has_goal"] and "1. p" in before["state"],
                  "step_proof": closed == [True, False, True] and bool(branches[1]["error"]),
                  "proof_branching": all(b["restored"]["state"] == before["state"] for b in branches)}
    output = args.output / "isabelle" / "isa-repl.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps({"prover": "isabelle", "environment_id": prepared.environment_id,
                                 "prover_build": prepared.spec.prover_build, "operations": operations,
                                 "runtime_roots": prepared.build["runtime_roots"], "native": trace},
                                indent=2, ensure_ascii=False) + "\n")
    _record(args.report, [{"prover": "isabelle", "operation": key, "environment_id": prepared.environment_id,
                          "prover_build": prepared.spec.prover_build,
                          "status": "implemented/tested" if ok else "failed",
                          "evidence_path": str(output.relative_to(args.report.parent))}
                         for key, ok in operations.items()])
    return 0 if all(operations.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
