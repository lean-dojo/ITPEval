"""Check a detached Sprig certificate and emit a typed kernel receipt."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from kernel import check_assumptions, clause_statement
from source import parse_problem, read_json


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    args = parser.parse_args()
    request = json.loads(args.request.read_bytes())
    if request.get("schema_version") != 1 or request.get("operation") != "proof_completion":
        raise ValueError("unsupported detached proof request")
    target = request["target"]
    problem_bytes = Path(target["source_path"]).read_bytes()
    proof_bytes = Path(request["proof_file"]).read_bytes()
    problem, _, (start, end) = parse_problem(problem_bytes)
    observed = {"schema_version": 1, "name": "goal", "source_path": target["source_path"],
                "start_byte": start, "end_byte": end, "statement": clause_statement(problem["goal"]),
                "source_sha256": sha256(problem_bytes), "statement_sha256": sha256(problem_bytes[start:end])}
    if observed != target:
        raise ValueError("the request does not identify the actual Sprig goal")
    detail = ""
    try:
        assumptions = check_assumptions(problem, read_json(proof_bytes))
        status = "accepted"
    except ValueError as exc:
        assumptions, status, detail = (), "rejected", str(exc)
    identity = {key: request[key] for key in ("task_id", "environment_id", "artifact_id")}
    inputs = {name: sha256(Path(name).read_bytes()) for name in request["inputs"]}
    print(json.dumps({"schema_version": 1, **identity, "target": observed, "inputs": inputs,
                      "proof_sha256": sha256(proof_bytes), "status": status, "assumptions": assumptions,
                      "detail": detail}))


if __name__ == "__main__":
    main()
