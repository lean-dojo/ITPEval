"""Bounded Lean tactic search guided by native goal observations."""

import argparse
from collections import deque
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, require_capabilities
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.runtime.interaction import LeanTacticSession
from itpeval.verification.fragments import permitted

REQUIRED = ("inspect_goals", "step_proof", "proof_completion")


def search(prepared, output: Path, *, max_nodes=12, max_depth=2, qualification_report=None):
    """Return final checker evidence, or None when the search budget is exhausted."""
    if prepared.spec.prover != "lean4" or min(max_nodes, max_depth) < 1:
        raise ValueError("Lean search requires a Lean project and positive node and depth budgets")
    require_capabilities("lean4", REQUIRED, prepared=prepared, qualification_report=qualification_report,
                         allow_experimental=qualification_report is None)
    task = build_task(prepared)
    session = LeanTacticSession(task, prepared)
    atoms = sorted(set(task.proof_atoms))
    if not atoms:
        raise ValueError("the task must declare composable tactics")
    queue = deque((atom,) for atom in atoms)
    steps, visited = [], set()
    final = None
    while queue and len(steps) < max_nodes:
        path = queue.popleft()
        candidate = " <;> ".join(path)
        if not permitted("lean4", candidate, task.allowed_edits, task.proof_atoms):
            continue
        initial = session.reset()
        handle, observation = session.step(initial, candidate)
        after = observation["after"]
        item = {"candidate": candidate, "before": observation["before"], "after": after}
        steps.append(item)
        if handle == initial:
            continue
        goals = tuple(after["goal"]["goals"])
        if not goals:
            final = session.finalize(handle)
            item["verification"] = final.to_dict()
            if final.task_success is not False:
                break
        elif goals not in visited and len(path) < max_depth:
            visited.add(goals)
            queue.extend((*path, atom) for atom in atoms)
    output.parent.mkdir(parents=True, exist_ok=True)
    jsonl(output, [{"schema_version": 1, "task_id": task.task_id, "environment_id": task.environment_id,
                    "algorithm": "breadth_first_tactics", "required_capabilities": REQUIRED,
                    "max_nodes": max_nodes, "max_depth": max_depth, "steps": steps,
                    "final": final.to_dict() if final else None}])
    return final


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("prefix", "cache", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--qualification-report", type=Path, help="require exact environment/build qualification")
    args = parser.parse_args()
    project = prepare_project("lean4", curated_project("lean4"), prefix=args.prefix, cache=args.cache)
    result = search(project, args.output, qualification_report=args.qualification_report)
    raise SystemExit(0 if result and result.task_success is True else 1)
