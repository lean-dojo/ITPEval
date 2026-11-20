"""Export a DIMACS input and its reviewed UNSAT target."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify import dimacs_target, project_file


def _records(entrypoint):
    problem = Path(entrypoint)
    source = project_file(entrypoint).read_bytes()
    target = dimacs_target(entrypoint, source)
    yield {"schema_version": 1}
    yield {"type": "source", "path": entrypoint, "sha256": target["source_sha256"]}
    yield {"type": "declaration", "source_path": entrypoint, "name": "input_cnf", "kind": "hypothesis",
           "statement": source[target["start_byte"]:target["end_byte"]].decode("ascii"),
           "start_byte": 0, "end_byte": len(source), "visible": []}
    prior = [[entrypoint, "input_cnf"]]
    goal = {"type": "declaration", "source_path": entrypoint, "name": target["name"], "kind": "theorem",
            "statement": target["statement"], "start_byte": target["start_byte"], "end_byte": target["end_byte"],
            "visible": prior}
    manifest_file = problem.with_name("completion.json")
    if manifest_file.is_file():
        manifest = json.loads(project_file(manifest_file.as_posix()).read_bytes())
        if manifest["source_path"] == entrypoint:
            proof = project_file(manifest["proof_file"]).read_bytes()
            if proof:
                goal.update(proof_manifest=manifest_file.as_posix(), proof_sha256=sha256(proof).hexdigest(),
                            proof_used=prior)
    yield goal


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entrypoint", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with args.output.open("x", encoding="utf-8") as stream:
        for record in _records(args.entrypoint):
            stream.write(json.dumps(record) + "\n")


if __name__ == "__main__":
    main()
