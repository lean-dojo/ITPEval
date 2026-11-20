"""Qualify LeanDojo tactic traces and two Pantograph branches against the installed compiler."""
import argparse
import json
import os
from pathlib import Path

from itpeval.backends.lean4.tools import leandojo_trace, pantograph_trace
from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, require_capabilities
from itpeval.environments import prepare_project
from itpeval.environments.cache import sha256, write_json
from itpeval.learning.qualification import _record


def qualify(prefix, cache, output, report, instruments=None):
    directory = instruments or prefix / "auxiliary/lean4"
    provenance = json.loads((directory / "provenance.json").read_bytes())
    native = {"pantograph": directory / "pantograph", "leandojo_tracer": directory / "ExtractData.lean"}
    if any(provenance["sha256"][file.name] != sha256(file) for file in native.values()):
        raise ValueError("installed Lean instruments differ from their build receipt")
    env = prepare_project("lean4", curated_project("lean4"), prefix=prefix, cache=cache, toolchain_inputs=native)
    require_capabilities("lean4", ("proof_branching", "action_traces"), prepared=env)
    if env.build["version"] != provenance["lean_version"]:
        raise ValueError("Lean instrument build and project compiler versions differ")
    entry = build_task(env).artifact.entrypoint
    branches = pantograph_trace(env, "∀ x : Nat, x = x",
                                [(0, "intro x"), (1, "rfl"), (1, "exact Eq.refl x")])
    trace = leandojo_trace(env, entry)
    steps = branches["transitions"]
    operations = {
        "proof_branching": (len(steps) == 3 and bool(branches["initial"]["goals"])
                            and bool(steps[0]["response"].get("goals"))
                            and all(step["parent"] == 1 and step["response"].get("goals") == []
                                    and step["response"].get("hasSorry") is False
                                    and step["response"].get("hasUnsafe") is False for step in steps[1:])),
        "action_traces": (trace["source_hash"] == sha256(env.project / entry)
                          and bool(trace["trace"]["commandASTs"] and trace["trace"]["premises"])
                          and any("⊢ x = x" in t["stateBefore"] and t["stateAfter"] == "no goals"
                                  for t in trace["trace"]["tactics"])),
    }
    path = output / "lean4/optional-tools.json"
    write_json(path, {"prover": "lean4", "environment_id": env.environment_id, "prover_build": env.spec.prover_build,
                      "operations": operations, "provenance": provenance,
                      "native": {"pantograph": branches, "leandojo": trace}})
    _record(report, [{"prover": "lean4", "environment_id": env.environment_id, "prover_build": env.spec.prover_build,
                      "operation": name, "status": "implemented/tested" if passed else "failed",
                      "evidence_path": os.path.relpath(path, report.parent)} for name, passed in operations.items()])
    return all(operations.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prefix", "cache", "output", "report"):
        parser.add_argument("--" + option, required=True, type=Path)
    parser.add_argument("--instruments", type=Path, help="the two installed instruments and their build receipt")
    raise SystemExit(0 if qualify(**vars(parser.parse_args())) else 1)
