"""Create a local editor exercise from a packaged proof-completion task."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.verification.policies import reviewed_document_template


def create_practice(args):
    destination = (args.output or Path("build/practice") / args.prover).resolve()
    if destination.exists():
        raise ValueError(f"Workspace already exists at {destination}. Open it to continue or choose another --output.")
    prepared = prepare_project(args.prover, curated_project(args.prover),
                               prefix=Path(args.prefix), cache=args.cache)
    task = build_task(prepared)
    template = reviewed_document_template(task, prepared)
    if template is None:
        raise ValueError("The packaged exercise needs a reviewed proof slot.")
    region, = task.editable_regions
    # Begin at the same unsuccessful edit that the prerecorded demonstration tries first.
    starter = task.allowed_edits[1]
    source = template[:region.start] + starter.encode("utf-8") + template[region.end:]
    entrypoint = task.artifact.entrypoint
    destination.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=destination.parent) as temp:
        project = Path(temp) / "workspace"
        for item in task.artifact.files:
            target = project / item.path
            target.parent.mkdir(parents=True, exist_ok=True)
            data = source if item.path == entrypoint else (prepared.project / item.path).read_bytes()
            target.write_bytes(data)
        # Elan can select the corresponding release for the Lean editor session.
        if args.prover == "lean4":
            version = re.search(r"Lean \(version (\d+\.\d+\.\d+(?:-rc\d+)?),", prepared.build["version"])
            if version:
                (project / "lean-toolchain").write_text(f"leanprover/lean4:v{version[1]}\n", encoding="utf-8")
        # The task checks the saved entrypoint against the original lock, including locked siblings.
        config = {"version": "2.0.0", "tasks": [{
            "label": "ITPEval: Check saved proof", "type": "process", "command": sys.executable,
            "args": ["-m", "itpeval.cli", "verify-task", "--lock", str(prepared.lock_path),
                     "--document-file", "${workspaceFolder}/" + entrypoint, "--summary"],
            "group": {"kind": "test", "isDefault": True}, "problemMatcher": [],
        }]}
        (project / ".vscode").mkdir()
        (project / ".vscode/tasks.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
        project.rename(destination)
    print(f"Open folder: {destination}")
    print(f"Edit {entrypoint} at {task.targets[0]}. Starting fragment: {starter}")
    print("Save, then choose Terminal > Run Task > ITPEval: Check saved proof.")
    print(f"Environment lock: {prepared.lock_path}")
    return 0
