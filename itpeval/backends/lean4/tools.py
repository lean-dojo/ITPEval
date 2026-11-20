"""Optional LeanDojo-v2 tracing and Pantograph native command trajectories."""
import hashlib
import json
import os
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

from itpeval.backends.projects import project_file
from itpeval.runtime.process import run_process


def _context(prepared, role):
    if prepared.spec.prover != "lean4":
        raise ValueError("this adapter requires Lean 4")
    prepared.validate()
    tool = dict(prepared.extra_inputs).get("external/" + role)
    if tool is None or not tool.is_file():
        raise ValueError(f"include the {role} file in prepare_project(toolchain_inputs=...)")
    lean = prepared.prefix / "lean4/bin/lean"
    prefix = run_process([str(lean), "--print-prefix"], timeout_s=15)
    if prefix.returncode:
        raise RuntimeError(prefix.stderr)
    sysroot = Path(prefix.stdout.strip())
    env = {k: os.environ[k] for k in ("HOME", "PATH", "LC_ALL", "LANG") if k in os.environ}
    env["PATH"] = str(sysroot / "bin") + os.pathsep + env["PATH"]
    env["LEAN_SYSROOT"] = str(sysroot)
    env["LEAN_PATH"] = os.pathsep.join([*(str(path) for _, path in prepared.library_paths),
                                        str(sysroot / "lib/lean")])
    return tool, lean, sysroot, env


def pantograph_trace(prepared, expression: str, actions, *, imports=("Init",), timeout_s=60):
    """Return native goal states in one isolated REPL invocation.

    Each action is (parent_state_index, tactic). Successful branches receive
    successive state IDs. A failed action stops the trace before any descendant
    can be mistaken for a different native state. These observations are for
    trusted local search and do not establish task success.
    """
    tool, _, _, env = _context(prepared, "pantograph")
    commands = [("goal.start", {"expr": expression}), ("goal.print", {"stateId": 0, "goals": True})]
    actions = list(actions)
    for expected, (parent, tactic) in enumerate(actions, 1):
        if type(parent) is not int or not 0 <= parent < expected or not isinstance(tactic, str):
            raise ValueError("each tactic requires an earlier native state index")
        commands.append(("goal.tactic", {"stateId": parent, "tactic": tactic}))
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        driver = root / "input"
        driver.write_text("".join(f"{name} {json.dumps(args, ensure_ascii=False)}\n"
                                  for name, args in commands) + "\n")
        result = run_process([str(tool), *imports], cwd=root, env=env, stdin_path=driver,
                             timeout_s=timeout_s)
    lines = result.stdout.splitlines()
    if result.returncode or result.outcome != "exited" or result.truncated or not lines or lines[0] != "ready.":
        raise RuntimeError(f"Pantograph failed: {result.stderr[-1500:]}")
    replies = [json.loads(line) for line in lines[1:] if line.strip()]
    if len(replies) != len(commands) or replies[0].get("stateId") != 0:
        raise ValueError(f"Pantograph could not start the requested goal: {replies[:1]}")
    trace = []
    for index, ((parent, tactic), reply) in enumerate(zip(actions, replies[2:]), 1):
        trace.append({"parent": parent, "action": tactic, "response": reply})
        if reply.get("nextStateId") != index:
            break
    return {"environment_id": prepared.environment_id, "expression": expression,
            "initial": replies[1], "transitions": trace}


def leandojo_trace(prepared, entrypoint: str, *, timeout_s=120):
    """Run the locked LeanDojo ExtractData frontend on a single project module."""
    tracer, lean, sysroot, env = _context(prepared, "leandojo_tracer")
    source = project_file(prepared.project, entrypoint)
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        shutil.copytree(prepared.project, root, dirs_exist_ok=True)
        packages = root / ".lake/packages"
        packages.mkdir(parents=True, exist_ok=True)
        (packages / "lean4").symlink_to(sysroot, target_is_directory=True)
        lib = root / ".lake/build/lib/lean"
        lib.mkdir(parents=True, exist_ok=True)
        module = lib / Path(entrypoint).with_suffix(".olean")
        module.parent.mkdir(parents=True, exist_ok=True)
        env["LEAN_PATH"] = os.pathsep.join([str(lib), str(root), env["LEAN_PATH"]])
        for command in ([str(lean), "-o", str(module), entrypoint],
                        [str(lean), "--run", str(tracer), entrypoint]):
            result = run_process(command, env=env, cwd=root, timeout_s=timeout_s)
            if result.returncode or result.outcome != "exited" or "PANIC at" in result.stderr:
                raise RuntimeError(f"LeanDojo tracing failed: {result.stderr[-1500:]}")
        base = root / ".lake/build/ir" / entrypoint
        trace = json.loads(base.with_suffix(".ast.json").read_bytes())
        imports = base.with_suffix(".dep_paths").read_text().splitlines()
        return {"environment_id": prepared.environment_id, "source_hash": hashlib.sha256(
                source.read_bytes()).hexdigest(), "trace": trace, "imports": imports}
