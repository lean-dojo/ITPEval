"""Bounded mutual implication for two Lean propositions in one extracted environment."""

from __future__ import annotations

import json
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path

from itpeval.core.declarations import FormalObject
from itpeval.core.records import Record, digest
from itpeval.corpus.storage import project_file, read_jsonl
from itpeval.extraction import extract_project
from itpeval.runtime.process import run_process


@dataclass(frozen=True)
class EquivalenceResult(Record):
    environment_id: str
    left_id: str
    right_id: str
    status: str
    forward: str
    backward: str
    diagnostic: str


def compare(prepared, entrypoint: str, left_id: str, right_id: str, *, cache: Path,
            timeout_s: int = 60) -> EquivalenceResult:
    """Compile the extracted module and kernel-check both implications in a fresh workspace."""
    if prepared.spec.prover != "lean4":
        raise ValueError("the bounded equivalence checker accepts Lean 4 declarations")
    prepared.validate()
    bundle = extract_project(prepared, entrypoint, cache, timeout_s=timeout_s)
    declarations = {row["declaration_id"]: FormalObject.from_dict(row)
                    for row in read_jsonl(bundle.path / "declarations.jsonl")}
    left, right = declarations[left_id], declarations[right_id]
    if left.environment_id != prepared.environment_id or right.environment_id != prepared.environment_id:
        raise ValueError("declarations belong to a different environment")
    module = ".".join(Path(entrypoint).with_suffix("").parts)
    for name in (module, left.name, right.name):
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in name.split(".")):
            raise ValueError(f"unsupported Lean identifier: {name!r}")

    def result(forward="", backward="", diagnostic=""):
        ok = forward in _STRATEGIES and backward in _STRATEGIES
        return EquivalenceResult(prepared.environment_id, left_id, right_id,
                                 "equivalence established" if ok else "equivalence not established",
                                 forward, backward, diagnostic)

    with tempfile.TemporaryDirectory() as directory:
        work = Path(directory)
        libpath = [str(work)]
        for _, library in prepared.library_paths:
            lib = Path(library) / ".lake/build/lib/lean"
            libpath.append(str(lib if lib.is_dir() else library))
        env = {**os.environ, "LEAN_PATH": os.pathsep.join(libpath)}
        lean = prepared.prefix / "lean4/bin/lean"
        options = ["-D" + key + "=" + value for key, value in prepared.spec.options]

        def run(*argv):
            return run_process([str(lean), *options, *map(str, argv)], cwd=work, env=env, timeout_s=timeout_s)

        for source in bundle.report["succeeded"]:
            source_path = project_file(prepared.project, source)
            target = work / source
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source_path.read_bytes())
            compiled = run("-o", Path(source).with_suffix(".olean"), source)
            if compiled.returncode:
                return result(diagnostic=compiled.stderr or compiled.stdout or compiled.outcome)
        driver = Path(__file__).with_name("CheckDirections.lean").read_text(encoding="utf-8")
        names = digest([left_id, right_id])[:16]
        driver = (f"import {module}\n" + driver + "\nrun_cmd liftTermElabM do\n"
                  + f"  let forward ← direction `{left.name} `{right.name} `ITPEval.forward_{names}\n"
                  + f"  let backward ← direction `{right.name} `{left.name} `ITPEval.backward_{names}\n"
                  + '  IO.println ("ITPEVAL_BEQ " ++ (toJson #[forward, backward]).compress)\n')
        tmp = work / ("Check" + names + ".lean")
        tmp.write_text(driver, encoding="utf-8")
        checked = run(tmp)
        if checked.returncode:
            return result(diagnostic=checked.stderr or checked.stdout or checked.outcome)
        for line in reversed(checked.stdout.splitlines()):
            if line.startswith("ITPEVAL_BEQ "):
                return result(*json.loads(line.removeprefix("ITPEVAL_BEQ ")))
        return result(diagnostic="checker produced no bidirectional result")


_STRATEGIES = {"exact", "symmetry", "swap_conjuncts"}
