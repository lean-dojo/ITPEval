"""Observe stock Isar proof states or branch with the optional Isa-REPL."""
from __future__ import annotations

import importlib.util
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from itpeval.backends.projects import project_file
from itpeval.core.records import Record
from itpeval.core.types import Artifact, TaskSpec
from itpeval.environments import PreparedProject
from itpeval.runtime.interaction import _ProofSession
from itpeval.runtime.process import run_process
from itpeval.verification.policies import assemble, reviewed, validate_inputs


_SESSION = re.compile(r'^\s*session\s+(?:"[^"]+"|[\w.-]+)\s*=\s*(?:"([\w.-]+)"|([\w.-]+))\s*\+', re.M)
_MESSAGE = re.compile(r'^(Output|Warning|Error) \(line (\d+) of "([^"]+)"\):[^\S\n]*$', re.M)
_GOALS = re.compile(r"^goal \((\d+) subgoals?\b", re.M)
_ERROR_BLOCK = re.compile(r"^(?:\*\*\*[^\n]*(?:\n|$))+", re.M)
_POSITION = re.compile(r'\(line (\d+) of "([^"]+)"\)')


@dataclass(frozen=True)
class IsabelleGoal(Record):
    candidate_line: int | None
    subgoal_count: int
    state: str


@dataclass(frozen=True)
class IsabelleProofState(Record):
    task_id: str
    environment_id: str
    source_path: str
    source_line: int
    target: str
    candidate: str | None
    goals: tuple[IsabelleGoal, ...]
    theory_checked: bool
    diagnostic: str | None


def _proof_states(log, source, probes):
    states = {}
    messages = list(_MESSAGE.finditer(log))
    for index, match in enumerate(messages):
        line = int(match[2])
        if match[1] != "Output" or Path(match[3]) != source or line not in probes:
            continue
        end = messages[index + 1].start() if index + 1 < len(messages) else len(log)
        state = re.split(r"\n(?:Finished |Unfinished session|.* FAILED |\*\*\*)",
                         log[match.end():end], maxsplit=1)[0].strip()
        count = _GOALS.search(state) if state.startswith("proof (") else None
        if count is not None:
            states[line] = IsabelleGoal(probes[line], int(count[1]), state)
        elif state.startswith("proof (") and "No subgoals!" in state:
            states[line] = IsabelleGoal(probes[line], 0, state)
    return tuple(states[line] for line in sorted(states))


def _only_errors_after_slot(log, source, line):
    positions = [(match[2], match[3]) for match in _MESSAGE.finditer(log) if match[1] == "Error"]
    for block in _ERROR_BLOCK.finditer(log):
        located = _POSITION.findall(block[0])
        if not located:
            return False
        positions.extend(located)
    return bool(positions) and all(int(at) > line and Path(file) == source for at, file in positions)


class IsabelleProofSession(_ProofSession):
    """Read the original proof goal and trace standalone Isar apply commands."""

    prover = "isabelle"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        if prepared.spec.checking_profile != "strict":
            raise ValueError("Isabelle proof observation requires a strict profile")
        self._region = task.editable_regions[0]
        if self._region.path != task.artifact.entrypoint:
            raise ValueError("the editable Isabelle theory must be the entrypoint")
        files = {item.path: item.data for item in task.artifact.files}
        parents = _SESSION.findall(files.get("ROOT", b"").decode())
        if len(parents) != 1:
            raise ValueError("expected one Isabelle session with an installed parent heap")
        self._parent = next(parent for parent in parents[0] if parent)
        self._line = files[self._region.path][:self._region.start].count(b"\n") + 1
        self._state = None

    def reset(self):
        self._state = None
        return super().reset()

    def _observe(self, candidate, cancel):
        probes = {self._line: None}
        if candidate is None:
            # Observe the original locked declaration even if its starter proof
            # fails. The allowed edits constrain submitted candidates.
            slot = self._region
            files = {item.path: item.data for item in self.task.artifact.files}
            original = project_file(self.prepared.project, slot.path).read_bytes()
            files[slot.path] = original[:slot.start] + b"print_state\n" + original[slot.start:]
            artifact = Artifact.from_files(self.task.artifact.entrypoint, files)
        else:
            assemble(self.task, candidate)
            lines = ["print_state"]
            for number, line in enumerate(candidate.split("\n"), 1):
                lines.append(line)
                # Insert observations after standalone Isar apply commands.
                # A multi-line method remains one uninstrumented fragment.
                if re.fullmatch(r"\s*apply \([^\r\n]*\)\s*", line):
                    probes[self._line + len(lines)] = number
                    lines.append("print_state")
            artifact = self._editor_source("\n".join(lines))
        validate_inputs(self.task, artifact)
        self.prepared.validate()
        budgets = self.task.budgets
        with tempfile.TemporaryDirectory(prefix="itpeval-isabelle-goals-") as temp:
            work = Path(temp)
            home, source = work / "home", work / "project"
            home.mkdir()
            artifact.materialize(source)
            env = {k: os.environ[k] for k in ("HOME", "PATH", "USER", "LANG", "LC_ALL") if k in os.environ}
            env.update(self.prepared.environment)
            env["USER_HOME"] = str(home)
            isabelle = self.prepared.prefix / "isabelle/bin/isabelle"
            theory = Path(artifact.entrypoint).with_suffix("").as_posix()
            result = run_process([str(isabelle), "process_theories", "-D", str(source), "-O",
                                  "-l", self._parent, "-o", "quick_and_dirty=false",
                                  "-o", "threads=2", "-o", "parallel_proofs=0", theory],
                                 cwd=source, env=env, cancel=cancel,
                                 timeout_s=budgets.timeout_s, max_log_bytes=budgets.max_log_bytes,
                                 memory_bytes=budgets.memory_bytes, cpu_seconds=budgets.cpu_seconds)
            if result.outcome != "exited" or result.truncated:
                raise RuntimeError(f"Isabelle proof observation failed ({result.outcome})")
            entry = source / artifact.entrypoint
            goals = _proof_states(result.stdout, entry, probes)
            raw_log = result.stdout + "\n" + result.stderr
            later_error = result.returncode and _only_errors_after_slot(raw_log, entry, self._line)
            log = raw_log.replace(str(source) + "/", "")
        if result.returncode and 'Unknown Isabelle tool: "process_theories"' in log:
            raise NotImplementedError("this Isabelle build does not provide process_theories for stock proof states")
        if (candidate is None or not result.returncode) and (not goals or goals[0].candidate_line is not None
                                                             or not goals[0].subgoal_count):
            raise ValueError("Isabelle did not report an open proof at the prepared slot")
        if candidate is None and result.returncode and not later_error:
            raise ValueError("Isabelle failed to establish the native proof context at the prepared slot")
        errors = [line for line in log.splitlines() if line.startswith("***")]
        diagnostic = ("\n".join(errors) or log[-2000:]) if result.returncode else None
        return IsabelleProofState(self.task.task_id, self.environment_id, artifact.entrypoint,
                                  self._line, self.task.targets[0], candidate, goals,
                                  result.returncode == 0, diagnostic)

    def inspect(self, handle, *, cancel=None):
        self.require(handle)
        if self._state is None:
            self._state = self._observe(None, cancel)
        return self._state

    def step(self, handle, candidate, *, cancel=None):
        self.require(handle)
        if not isinstance(candidate, str):
            raise ValueError("expected a reviewed Isabelle proof fragment")
        state = self._observe(candidate, cancel)
        if not state.theory_checked:
            return handle, state
        self._state = state
        self.candidate = candidate
        self.revision += 1
        return self.handle, state


def branch_trace(task: TaskSpec, candidates, *, prepared: PreparedProject, cancel=None) -> dict:
    """Evaluate authorized alternatives using the project's pinned Isa-REPL sources.

    Imports must be available in the HOL heap. The ephemeral checkpoint restores
    the proof state only. Each call owns its native process and its theory table.
    """
    if (task.prover != "isabelle" or task.operation != "proof_completion"
            or task.environment_id != prepared.environment_id or prepared.spec.checking_profile != "strict"
            or not reviewed(task, prepared)):
        raise ValueError("expected a reviewed Isabelle proof task in its prepared environment")
    prepared.validate()
    validate_inputs(task, task.artifact)
    actions = tuple(candidates)
    if not 0 < len(actions) <= 256:
        raise ValueError("expected one to 256 candidate revisions")
    for action in actions:
        assemble(task, action)
    tools = dict(prepared.extra_inputs)
    if not all("external/" + role in tools for role in ("isa_repl", "auto_sledgehammer")):
        raise ValueError("lock isa_repl and auto_sledgehammer trees using toolchain_inputs")
    if importlib.util.find_spec("msgpack") is None:
        raise ValueError("Isa-REPL requires the isabelle optional Python dependency")
    limits = task.budgets
    with tempfile.TemporaryDirectory(prefix="itpeval-isarepl-") as tmp:
        work = Path(tmp)
        slot = task.editable_regions[0]
        original = next(f.data for f in task.artifact.files if f.path == slot.path)
        spec = {"prologue": original[:slot.start].decode(), "candidates": actions,
                "isa_repl": str(tools["external/isa_repl"]),
                "auto_sledgehammer": str(tools["external/auto_sledgehammer"]),
                "isabelle": str(prepared.prefix / "isabelle/bin/isabelle")}
        (work / "request.json").write_text(json.dumps(spec))
        env = {k: os.environ[k] for k in ("HOME", "PATH", "USER", "LANG") if k in os.environ}
        env["PATH"] = str(Path(spec["isabelle"]).parent) + os.pathsep + env.get("PATH", "")
        env.update(prepared.environment)
        # The supervisor owns both the protocol client and Isabelle's descendants.
        # The upstream protocol client can block while reading a native response.
        job = run_process([sys.executable, "-B", str(Path(__file__).with_name("_repl_worker.py"))],
                          cwd=work, env=env, cancel=cancel, timeout_s=limits.timeout_s,
                          max_log_bytes=limits.max_log_bytes, cpu_seconds=limits.cpu_seconds,
                          memory_bytes=limits.memory_bytes)
        output = work / "observations.json"
        if job.returncode or job.outcome != "exited" or not output.is_file():
            raise RuntimeError(f"Isa-REPL failed ({job.outcome}): {(job.stdout + job.stderr)[-2400:]}")
        if output.stat().st_size > limits.max_log_bytes:
            raise ValueError("Isa-REPL trace exceeds the task's output budget")
        return {"environment_id": task.environment_id, "task_id": task.task_id,
                **json.loads(output.read_text())}
