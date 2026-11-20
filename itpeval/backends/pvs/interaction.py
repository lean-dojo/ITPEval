"""Inspect and replay ordered PVS proof commands in isolated native transactions."""
from __future__ import annotations

import json
import os
import re
import tempfile
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from threading import RLock
from typing import Literal

from itpeval.core.records import Record, digest
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.environments import PreparedProject
from itpeval.runtime.interaction import _ProofSession
from itpeval.runtime.process import run_process
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import assemble, reviewed, validate_inputs
from itpeval.verification.service import verify


_OPEN = ("init", "waiting")
PVS_AUTOMATION_STRATEGIES = ("(grind)", "(assert)")


class PVSReplayFailure(RuntimeError):
    def __init__(self, outcome: str, diagnostic: str):
        self.outcome = outcome
        super().__init__(f"PVS command replay failed ({outcome}): {diagnostic}")


def command_trace(task: TaskSpec, commands: Iterable[str], *, prepared: PreparedProject,
                  cancel=None, timeout_s: float | None = None) -> list[dict]:
    """Return the initial state and one native observation per command.

    PVS starts a fresh proof of the named formula in an isolated directory on
    each replay. A terminal sequent concerns that formula. Use verify for final
    task acceptance, including the task's separate type-correctness obligations.
    """
    rows, _ = _transaction(task, commands, prepared, cancel, timeout_s=timeout_s)
    return rows


def _allowed(task, command):
    return isinstance(command, str) and permitted(
        "pvs", command, task.allowed_edits + task.proof_atoms, task.proof_atoms,
    )


def review_pvs_automation(task: TaskSpec, command: str, *, proof_fragment: str | None = None) -> str | None:
    """Validate a native auto strategy and any explicit final ProofLite fragment.

    The final fragment is independently checked on the locked formula and TCCs
    after the interactive proof closes. Its syntax need not encode the command history.
    """
    if task.prover != "pvs" or task.operation != "proof_completion":
        raise ValueError("expected a PVS proof completion task")
    if command not in PVS_AUTOMATION_STRATEGIES or not _allowed(task, command):
        raise ValueError("PVS automation strategy is outside the task policy")
    if proof_fragment is not None:
        if not isinstance(proof_fragment, str):
            raise ValueError("expected an explicit reviewed ProofLite fragment")
        assemble(task, proof_fragment)
    return proof_fragment


def _transaction(task, commands, prepared, cancel, *, timeout_s=None, observe_horn=False):
    if (task.prover != "pvs" or prepared.spec.prover != "pvs" or task.operation != "proof_completion"
            or task.environment_id != prepared.environment_id or prepared.spec.checking_profile != "strict"
            or not reviewed(task, prepared)):
        raise ValueError("expected a PVS proof task bound to the prepared project")
    prepared.validate()
    validate_inputs(task, task.artifact)
    if timeout_s is not None and not 0 < timeout_s <= task.budgets.timeout_s:
        raise ValueError("PVS replay timeout must be positive and fit the task's wall budget")
    actions = list(commands)
    if len(actions) > 256 or any(not _allowed(task, cmd) for cmd in actions):
        raise ValueError("PVS command outside task policy")
    entry = Path(task.artifact.entrypoint)
    slot = task.editable_regions[0]
    sources = {file.path: file.data for file in task.artifact.files}
    if entry.suffix != ".pvs" or slot.path != task.artifact.entrypoint:
        raise ValueError("expected a PVS proof slot in the entrypoint theory file")
    before = sources[slot.path][:slot.start].decode("utf-8")
    target = task.targets[0].rsplit(".", 1)[-1]
    declaration = re.compile(r"^[ \t]*" + re.escape(target) + r"\s*:\s*(?:LEMMA|THEOREM)\b", re.I | re.M)
    locators = list(declaration.finditer(before))
    if not locators:
        raise ValueError("PVS proof slot does not follow the reviewed formula")
    target_line = before.count("\n", 0, locators[-1].start()) + 1
    with tempfile.TemporaryDirectory(prefix="itpeval-pvs-commands-") as work:
        root = Path(work)
        src = root / "source"
        task.artifact.materialize(src)
        out = root / "states"
        action_file = root / "commands.json"
        action_file.write_text(json.dumps(actions), encoding="utf-8")
        env = {k: os.environ[k] for k in ("HOME", "PATH", "USER", "LANG") if k in os.environ}
        env.update(prepared.environment)
        env.update(ITPEVAL_COMMANDS=str(action_file), ITPEVAL_OUTPUT=str(out), PVSMINUSQ="t",
                   PVS_LOG_DIR=str(root / "log"), ITPEVAL_ENTRY=str(entry.with_suffix("")),
                   ITPEVAL_TARGET=target, ITPEVAL_TARGET_LINE=str(target_line))
        horn_file = root / "horn.json"
        if observe_horn:
            env["ITPEVAL_HORN_OUTPUT"] = str(horn_file)
        else:
            env.pop("ITPEVAL_HORN_OUTPUT", None)
        driver = Path(__file__).resolve().parents[2] / "extraction/native/pvs_commands.lisp"
        # The trace is closed before exit. An unfinished proof can leave a
        # native SBCL thread waiting, so skip the normal interactive shutdown.
        evaluate = "(progn (itpeval-replay-commands) (sb-ext:exit :abort t :code 0))"
        result = run_process([str(prepared.prefix / "pvs/bin/pvs"), "-raw", "-L", str(driver),
                              "-E", evaluate], cwd=src, env=env,
                             cancel=cancel, timeout_s=task.budgets.timeout_s if timeout_s is None else timeout_s,
                             max_log_bytes=task.budgets.max_log_bytes,
                             cpu_seconds=task.budgets.cpu_seconds, memory_bytes=task.budgets.memory_bytes)
        if result.outcome != "exited":
            raise PVSReplayFailure(result.outcome, (result.stderr + result.stdout)[-2500:])
        if result.returncode or not out.exists():
            raise RuntimeError(f"PVS command replay failed ({result.outcome}): {result.stderr + result.stdout}")
        if out.stat().st_size > task.budgets.max_log_bytes:
            raise ValueError("native PVS trace exceeds the task's output budget")
        lines = out.read_text(encoding="utf-8").splitlines()
        if not lines or lines.pop() != "complete" or len(lines) != len(actions) + 2:
            raise ValueError("incomplete native PVS trace: " + result.stdout[-1200:])
        tag, theory_name = lines.pop(0).split("\t", 1)
        if tag != "theory" or not theory_name:
            raise ValueError("PVS did not identify the target's typechecked theory")
        observations = []
        for cmd, line in zip([None, *actions], lines):
            status, states, failure = line.split("\t", 2)
            observations.append({"command": cmd, "status": status, "states": json.loads(states), "theory": theory_name,
                                 "error": json.loads(failure),
                                 "task_id": task.task_id, "environment_id": task.environment_id})
        if observe_horn and horn_file.is_file():
            if out.stat().st_size + horn_file.stat().st_size > task.budgets.max_log_bytes:
                raise ValueError("native PVS observations exceed the task's output budget")
            observations[-1]["horn"] = json.loads(horn_file.read_text(encoding="utf-8"))
        return observations, src


@dataclass(frozen=True)
class PVSSymbol(Record):
    name: str
    declaration: str | None
    declaration_path: str | None
    declaration_range: tuple[int, ...]
    occurrence_range: tuple[int, ...]


@dataclass(frozen=True)
class PVSFormula(Record):
    labels: tuple[int, ...]
    text: str
    symbols: tuple[PVSSymbol, ...]


@dataclass(frozen=True)
class PVSSequent(Record):
    antecedents: tuple[PVSFormula, ...]
    succedents: tuple[PVSFormula, ...]


@dataclass(frozen=True)
class PVSGoalEvent(Record):
    path: str
    label: str
    status: str
    action: str
    sequent: PVSSequent | None
    commentary: tuple[str, ...]


@dataclass(frozen=True)
class PVSProofState(Record):
    task_id: str
    environment_id: str
    source_path: str
    theory: str
    target: str
    command: str | None
    status: str
    events: tuple[PVSGoalEvent, ...]
    error: str | None = None

    @property
    def focused(self) -> PVSGoalEvent | None:
        return self.events[-1] if self.status in _OPEN and self.events else None

    @property
    def state_digest(self) -> str:
        # Native commentary includes startup timestamps and timings.
        data = self.to_dict()
        for event in data["events"]:
            del event["commentary"]
        return digest(data)


@dataclass(frozen=True)
class PVSProofCheckpoint(Record):
    task_id: str
    environment_id: str
    commands: tuple[str, ...]
    state_digest: str | None


@dataclass(frozen=True)
class PVSFinalization(Record):
    target: str
    theory: str
    checkpoint: PVSProofCheckpoint
    proof_fragment: str
    match: Literal["identical_native_command", "same_locked_target"]
    verification: VerificationEvidence

    @property
    def task_success(self) -> bool | None:
        return self.verification.task_success


def _native_state(raw, task, source, prepared):
    toolchain = prepared.prefix / "pvs"

    def path(value):
        if value is None:
            return None
        native = Path(value)
        if native.is_relative_to(source):
            return native.relative_to(source).as_posix()
        if native.is_relative_to(toolchain):
            return "toolchain/pvs/" + native.relative_to(toolchain).as_posix()
        return None if native.is_absolute() else native.as_posix()

    def formula(row):
        symbols = tuple(PVSSymbol(item["id"], item.get("decl"), path(item.get("decl-file")),
                                  tuple(item.get("decl-place") or ()), tuple(item.get("place") or ()))
                        for item in row.get("names-info") or ())
        return PVSFormula(tuple(row.get("labels") or ()), row["formula"], symbols)

    def event(row):
        value = row.get("sequent")
        sequent = (PVSSequent(tuple(formula(x) for x in value.get("antecedents") or ()),
                             tuple(formula(x) for x in value.get("succedents") or ()))
                   if value is not None else None)
        return PVSGoalEvent(row["path"], row["label"], row["status"], row["action"], sequent,
                            tuple(row.get("commentary") or ()))

    # PVS reports the visited proof events and next focus rather than all
    # then-pending siblings. Keep its labels and path without inferring nodes.
    state = PVSProofState(task.task_id, task.environment_id, task.artifact.entrypoint, raw["theory"], task.targets[0],
                          raw["command"], raw["status"], tuple(event(row) for row in raw["states"] or ()),
                          raw["error"])
    if state.error is None and state.status in _OPEN and (state.focused is None or state.focused.sequent is None):
        raise ValueError("PVS did not report a focused sequent")
    return state


class PVSProofSession(_ProofSession):
    """Step and branch by replaying the exact prefix of native prover commands."""

    prover = "pvs"

    def __init__(self, task: TaskSpec, prepared: PreparedProject):
        super().__init__(task, prepared)
        if task.operation != "proof_completion" or prepared.spec.checking_profile != "strict":
            raise ValueError("expected a strict PVS proof completion")
        validate_inputs(task, task.artifact)
        self._commands = ()
        self._state = None
        self._lock = RLock()

    def _replay(self, commands, cancel, *, allow_last_error=False, timeout_s=None):
        raw, source = _transaction(self.task, commands, self.prepared, cancel, timeout_s=timeout_s)
        confirmed = raw[:-1] if allow_last_error else raw
        if any(row["error"] is not None for row in confirmed):
            raise ValueError("a saved PVS command failed during native replay")
        return _native_state(raw[-1], self.task, source, self.prepared)

    def inspect(self, handle, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self._state is None:
                self._state = self._replay(self._commands, cancel)
            return self._state

    def observe_horn(self, handle, *, cancel=None, timeout_s=None):
        """Inspect the typed fragment at exactly the committed focused sequent."""
        with self._lock:
            state = self.inspect(handle, cancel=cancel)
            if state.focused is None:
                raise ValueError("PVS Horn search requires an open focused sequent")
            rows, source = _transaction(self.task, self._commands, self.prepared, cancel,
                                        timeout_s=timeout_s, observe_horn=True)
            replayed = _native_state(rows[-1], self.task, source, self.prepared)
            if any(row["error"] is not None for row in rows) or replayed.state_digest != state.state_digest:
                raise RuntimeError("PVS Horn observation differed from the committed native state")
            observation = rows[-1].get("horn")
            if observation is None or observation["path"] != state.focused.path:
                raise RuntimeError("PVS did not report the typed Horn fragment for the focused sequent")
            if observation["conclusion"] is not None:
                observation["conclusion"]["formula"] = state.focused.sequent.succedents[0].text
            for premise in observation["premises"]:
                premise["formula"] = state.focused.sequent.antecedents[-premise["label"] - 1].text
            return observation

    def step(self, handle, command, *, cancel=None, timeout_s: float | None = None):
        with self._lock:
            self.require(handle)
            if not _allowed(self.task, command) or len(self._commands) >= 256:
                raise ValueError("PVS command outside task policy")
            if self._state is not None and self._state.status not in _OPEN:
                raise ValueError("the PVS proof has already finished")
            commands = (*self._commands, command)
            state = self._replay(commands, cancel, allow_last_error=True, timeout_s=timeout_s)
            if state.error is not None:
                return self.handle, state
            self._state, self._commands = state, commands
            self.revision += 1
            return self.handle, state

    def reset(self):
        with self._lock:
            self._commands, self._state = (), None
            return super().reset()

    def replay_prefix(self, handle, commands, *, cancel=None):
        """Replay a committed command prefix in one native transaction.

        Return the initial state and every intermediate state. The session
        must be clean. A failed command leaves that session unchanged.
        """
        with self._lock:
            self.require(handle)
            if self._commands:
                raise ValueError("PVS replay_prefix requires an unused proof session")
            commands = tuple(commands)
            raw, source = _transaction(self.task, commands, self.prepared, cancel)
            if any(row["error"] is not None for row in raw) or any(row["status"] not in _OPEN for row in raw[:-1]):
                raise ValueError("saved PVS commands did not form a committed proof prefix")
            states = tuple(_native_state(row, self.task, source, self.prepared) for row in raw)
            self._commands, self._state = commands, states[-1]
            self.revision = len(commands)
            return states

    def fork(self, handle):
        with self._lock:
            self.require(handle)
            branch = PVSProofSession(self.task, self.prepared)
            branch._commands, branch._state = self._commands, self._state
            branch.revision = self.revision
            return branch

    def checkpoint(self, handle):
        with self._lock:
            self.require(handle)
            return PVSProofCheckpoint(self.task.task_id, self.environment_id, self._commands,
                                      self._state.state_digest if self._state is not None else None)

    @classmethod
    def from_checkpoint(cls, task, prepared, checkpoint: PVSProofCheckpoint, *, cancel=None):
        if (checkpoint.task_id, checkpoint.environment_id) != (task.task_id, prepared.environment_id):
            raise ValueError("PVS proof checkpoint belongs to another task or environment")
        if checkpoint.commands and checkpoint.state_digest is None:
            raise ValueError("a nonempty PVS checkpoint must identify the observed state")
        session = cls(task, prepared)
        state = session._replay(checkpoint.commands, cancel)
        if checkpoint.state_digest is not None and checkpoint.state_digest != state.state_digest:
            raise ValueError("PVS replay differed from the checkpoint's observed state")
        session._commands, session._state = checkpoint.commands, state
        session.revision = len(checkpoint.commands)
        return session

    def finalize(self, handle, proof_fragment=None, **options):
        """Check an explicit ProofLite strategy for the same locked formula and TCCs."""
        with self._lock:
            self.require(handle)
            if self._state is None or self._state.status != "proved":
                raise ValueError("finish the interactive PVS proof before finalizing it")
            if proof_fragment is None and len(self._commands) == 1:
                proof_fragment = self._commands[0]
            if not isinstance(proof_fragment, str):
                raise ValueError("supply an approved ProofLite fragment for this interactive command sequence")
            artifact = assemble(self.task, proof_fragment)
            evidence = verify(self.task, proof_fragment, prepared=self.prepared, **options)
            if evidence.task_success is True and evidence.artifact_id != artifact.artifact_id:
                raise RuntimeError("PVS verification returned another checked artifact")
            match = ("identical_native_command" if self._commands == (proof_fragment,)
                     else "same_locked_target")
            return PVSFinalization(self.task.targets[0], self._state.theory, self.checkpoint(handle),
                                   proof_fragment, match, evidence)
