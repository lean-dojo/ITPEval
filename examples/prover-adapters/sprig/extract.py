"""Emit source-grounded clauses and resolution dependencies for ITPEval."""

import argparse
import hashlib
import json
import sys
from pathlib import Path

# Isolated Python excludes the script directory. Add only the locked adapter.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from kernel import check_assumptions, clause_statement
from source import parse_problem, read_json


def _project_file(name):
    root = Path.cwd()
    relative = Path(name)
    path = (root / relative).resolve(strict=True)
    if (relative.is_absolute() or relative.as_posix() != name or ".." in relative.parts
            or not path.is_relative_to(root) or not path.is_file()):
        raise ValueError(f"expected a regular project file: {name!r}")
    return path


def _records(entrypoint):
    source = _project_file(entrypoint).read_bytes()
    problem, premises, goal = parse_problem(source)

    def declaration(name, kind, clause, span, visible):
        first, last = span
        return {"type": "declaration", "source_path": entrypoint, "name": name, "kind": kind,
                "statement": clause_statement(clause), "start_byte": first, "end_byte": last,
                "visible": visible}

    yield {"schema_version": 1}
    yield {"type": "source", "path": entrypoint, "sha256": hashlib.sha256(source).hexdigest()}
    visible = []
    for index, (clause, span) in enumerate(zip(problem["premises"], premises, strict=True)):
        name = f"premise_{index}"
        yield declaration(name, "hypothesis", clause, span, [])
        visible.append([entrypoint, name])

    target = declaration("goal", "theorem", problem["goal"], goal, visible)
    manifest_path = Path(entrypoint).with_name("completion.json").as_posix()
    if Path(manifest_path).is_file():
        manifest = read_json(_project_file(manifest_path).read_bytes())
        if not isinstance(manifest, dict):
            raise ValueError("Sprig completion manifest must be an object")
        if manifest.get("source_path") == entrypoint:
            proof_file = manifest.get("proof_file")
            if not isinstance(proof_file, str):
                raise ValueError("Sprig completion manifest must name its proof file")
            proof = _project_file(proof_file).read_bytes()
            if proof.strip():
                certificate = read_json(proof)
                target["proof_manifest"] = manifest_path
                target["proof_sha256"] = hashlib.sha256(proof).hexdigest()
                target["proof_used"] = [[entrypoint, name] for name in check_assumptions(problem, certificate)]
    yield target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entrypoint", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        with args.output.open("x", encoding="utf-8") as stream:
            for record in _records(args.entrypoint):
                stream.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n")
    except (OSError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
