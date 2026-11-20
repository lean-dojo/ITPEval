"""Observe Rocq proof commands through RocqIDE or a locked Pétanque shell."""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import json
import os
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from threading import RLock

from itpeval.core.records import Record
from itpeval.runtime.interaction import _ProofSession
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import assemble, reviewed, validate_inputs
from itpeval.runtime.process import run_process


def command_trace(task, commands, *, prepared, cancel=None):
    """Run commands on earlier native states. IDs expire at the end of the call.

    A command can be a tactic string to continue from the previous state or a
    (parent_index, tactic) pair to branch. Index zero is the original goal.
    The returned shelf and given-up lists accompany every successful response.
    """
    if (task.prover != "rocq" or prepared.spec.prover != "rocq" or
            prepared.spec.checking_profile != "strict" or task.operation != "proof_completion"
            or task.environment_id != prepared.environment_id or not reviewed(task, prepared)):
        raise ValueError("expected a reviewed Rocq proof task in the prepared environment")
    if task.dependency_sources:
        raise ValueError("the Pétanque adapter requires a single module with installed imports")
    prepared.validate()
    validate_inputs(task, task.artifact)
    tools = dict(prepared.extra_inputs)
    try:
        executable = tools["external/petanque"]
        library = tools["external/petanque_runtime"]
    except KeyError as exc:
        raise ValueError("prepare the petanque executable and petanque_runtime library directory") from exc
    actions = []
    for i, command in enumerate(commands):
        parent, tactic = (i, command) if isinstance(command, str) else command
        if (i >= 256 or type(parent) is not int or not 0 <= parent <= i or not isinstance(tactic, str)
                or not permitted("rocq", tactic, task.allowed_edits, task.proof_atoms)):
            raise ValueError("expected a reviewed Rocq command and an earlier state index")
        actions.append((parent, tactic))
    with TemporaryDirectory(prefix="itpeval-petanque-") as tmp:
        root = Path(tmp)
        src = root / "source"
        task.artifact.materialize(src)
        spec = root / "transaction.json"
        spec.write_text(json.dumps({"path": task.artifact.entrypoint, "target": task.targets[0],
                                    "actions": actions}))
        env = {k: os.environ[k] for k in ("HOME", "PATH", "LANG") if k in os.environ}
        # Select plugins and core libraries compiled with this embedded Rocq build.
        env.update(COQLIB=str(library / "coq"), COQCORELIB=str(library / "rocq-runtime"),
                   OCAMLPATH=str(library), OCAMLFIND_CONF=str(library / "findlib.conf"))
        budget = task.budgets
        result = run_process([sys.executable, str(Path(__file__).with_name("_pet.py")), str(executable), str(spec)],
                             cwd=src, env=env, cancel=cancel, timeout_s=budget.timeout_s,
                             memory_bytes=budget.memory_bytes, cpu_seconds=budget.cpu_seconds,
                             max_log_bytes=budget.max_log_bytes)
    if result.outcome != "exited" or result.returncode or result.truncated:
        raise RuntimeError(f"Pétanque transaction failed ({result.outcome}): {result.stderr[-1000:]}")
    return {"environment_id": task.environment_id, "task_id": task.task_id, "states": json.loads(result.stdout)}


@dataclass(frozen=True)
class RocqIDEState(Record):
    task_id: str
    environment_id: str
    source_path: str
    target: str
    command: str | None
    complete: bool
    goals: dict[str, str] | None
    error: str | None


class RocqIDESession(_ProofSession):
    """Use the stock Rocq compiler and IDE protocol without the Pétanque plugin."""

    prover = "rocq"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        self._reference = assemble(task, task.allowed_edits[0])
        validate_inputs(task, self._reference)
        if prepared.spec.checking_profile != "strict":
            raise ValueError("RocqIDE interaction requires a strict project profile")
        self._compiler = prepared.prefix / "rocq/bin/rocq"
        self._ide = self._compiler.resolve().with_name("coqidetop").resolve()
        if not self._ide.is_file():
            raise FileNotFoundError(f"RocqIDE executable unavailable at {self._ide}")
        self._history: list[str] = []
        self._spans: list = []
        self._state = None
        self._lock = RLock()

    def reset(self):
        with self._lock:
            self._history.clear()
            self._state = None
            return super().reset()

    def _trace(self, actions, cancel):
        flags = [option for name, lib in self.prepared.library_paths for option in ("-Q", str(lib), name)]
        entrypoint = self.task.artifact.entrypoint
        with TemporaryDirectory(prefix="itpeval-rocqide-") as temp:
            root = Path(temp)
            source = root / "project"
            self._reference.materialize(source)
            request = root / "request.json"
            request.write_text(json.dumps(
                {"entrypoint": entrypoint, "slot": self.task.editable_regions[0].start, "actions": actions,
                 "spans": self._spans, "timing": str(root / "timings"), "flags": flags,
                 "rocq": str(self._compiler), "ide": str(self._ide)}), encoding="utf-8")
            raw = self._run([sys.executable, "-B", str(Path(__file__).with_name("_ide.py")), str(request)],
                            source, cancel)
        result = json.loads(raw)
        self._spans = result["spans"]
        observations = result["observations"]
        if (not observations or len(observations) > len(actions) + 1
                or (len(observations) < len(actions) + 1 and observations[-1]["error"] is None)):
            raise RuntimeError("RocqIDE did not reproduce the prior successful commands")
        return tuple(RocqIDEState(self.task.task_id, self.environment_id, entrypoint, self.task.targets[0],
                                  **observation) for observation in observations)

    def inspect(self, handle, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self._state is None:
                self._state = self._trace(self._history, cancel)[-1]
            return deepcopy(self._state)

    def fork(self, handle):
        """Copy the committed commands, parser spans, and goal observation."""
        with self._lock:
            self.require(handle)
            child = RocqIDESession(self.task, self.prepared)
            child._history = self._history.copy()
            child._spans = deepcopy(self._spans)
            child._state = deepcopy(self._state)
            child.candidate, child.revision = self.candidate, self.revision
            return child

    def _require_command(self, history, command):
        if not isinstance(command, str) or not command.endswith(".") or len(history) >= 256:
            raise ValueError("expected a reviewed Rocq command ending in a period")
        if not any(permitted("rocq", text, self.task.allowed_edits, self.task.proof_atoms)
                   for text in (command, "\n".join((*history, command)))):
            raise ValueError("expected a reviewed Rocq command ending in a period")

    def step(self, handle, command, *, cancel=None):
        with self._lock:
            self.require(handle)
            self._require_command(self._history, command)
            actions = [*self._history, command]
            states = self._trace(actions, cancel)
            if len(states) != len(actions) + 1:
                raise RuntimeError("RocqIDE did not reproduce the prior successful commands")
            state = states[-1]
            if state.error is not None:
                return self.handle, state
            self._history = actions
            self._state = deepcopy(state)
            # Preserve periods between native commands. A semicolon would
            # apply the next tactic to every generated goal.
            self.candidate = "\n".join(actions)
            self.revision += 1
            return self.handle, state

    def replay_prefix(self, handle, commands, *, cancel=None):
        """Replay authorized commands in one IDE process, retaining each goal state."""
        with self._lock:
            self.require(handle)
            if self._history:
                raise ValueError("Rocq replay_prefix requires an unused proof session")
            history = []
            for command in commands:
                self._require_command(history, command)
                history.append(command)
            states = self._trace(history, cancel)
            if states[-1].error is not None:
                raise ValueError(f"saved Rocq command {len(states) - 1} did not replay")
            self._history, self._state = history, deepcopy(states[-1])
            self.candidate = "\n".join(history) if history else None
            self.revision = len(history)
            return states

    def finalize(self, handle, **options):
        with self._lock:
            return super().finalize(handle, **options)
