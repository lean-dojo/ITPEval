"""Run the pinned DRAT-trim checker on the exact staged DIMACS and proof files."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryFile


def project_file(name):
    root = Path.cwd()
    relative = Path(name)
    path = (root / relative).resolve(strict=True)
    if (relative.is_absolute() or relative.as_posix() != name or ".." in relative.parts
            or not path.is_relative_to(root) or not path.is_file()):
        raise ValueError(f"expected a regular project file: {name!r}")
    return path


def file_sha256(path):
    digest = sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def dimacs_target(source_path, source):
    headers = list(re.finditer(rb"(?m)^p cnf [0-9]+ [0-9]+(?=\r?$)", source))
    if len(headers) != 1:
        raise ValueError("expected one DIMACS header in the fixed source")
    header, = headers
    return {"schema_version": 1, "source_path": source_path, "name": "unsatisfiable",
            "start_byte": header.start(), "end_byte": header.end(), "statement": "UNSAT",
            "source_sha256": sha256(source).hexdigest(), "statement_sha256": sha256(header[0]).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    request = json.loads(parser.parse_args().request.read_bytes())
    if request["schema_version"] != 1 or request["operation"] != "proof_completion":
        raise ValueError("unsupported DRAT proof request")
    target = request["target"]
    problem = project_file(target["source_path"])
    proof = project_file(request["proof_file"])
    actual = dimacs_target(target["source_path"], problem.read_bytes())
    if actual != target:
        raise ValueError("the request does not identify this DIMACS formula")

    checker = Path(__file__).resolve().parent / "bin/drat-trim"
    with TemporaryFile() as log:
        result = subprocess.run([checker, problem, proof], stdin=subprocess.DEVNULL,
                                stdout=log, stderr=subprocess.STDOUT, check=False)
        size = log.seek(0, 2)
        log.seek(max(0, size - 8192))
        tail = log.read().decode("utf-8", errors="replace").splitlines()
    statuses = {line for line in tail if line.startswith("s ")}
    if result.returncode == 0 and statuses == {"s VERIFIED"}:
        status, assumptions = "accepted", ["input_cnf"]
    elif result.returncode == 1 and statuses == {"s NOT VERIFIED"}:
        status, assumptions = "rejected", []
    else:
        raise RuntimeError("DRAT-trim did not return a recognized verdict: " + "\n".join(tail))

    identity = {field: request[field] for field in ("task_id", "environment_id", "artifact_id")}
    print(json.dumps({"schema_version": 1, **identity, "target": actual,
                      "inputs": {name: file_sha256(project_file(name)) for name in request["inputs"]},
                      "proof_sha256": file_sha256(proof), "status": status, "assumptions": assumptions}))


if __name__ == "__main__":
    main()
