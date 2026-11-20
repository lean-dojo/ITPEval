"""Observe native HOL tactics at the proof slot of a locked completion task."""
from __future__ import annotations

import os
import tempfile
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from threading import RLock

from itpeval.core.records import Record
from itpeval.core.types import TaskSpec
from itpeval.environments import PreparedProject
from itpeval.extraction.native_io import observations
from itpeval.runtime.interaction import _ProofSession
from itpeval.runtime.process import run_process
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import reviewed, validate_inputs


class HOLTraceFailure(RuntimeError):
    def __init__(self, prover, outcome, diagnostic):
        super().__init__(f"{prover} trace failed ({outcome}): {diagnostic}")
        self.outcome = outcome


def _invocations(rows, actions):
    # THEN applies its right tactic to every remaining goal. The same command
    # may consequently have zero, one or several separate invocations.
    calls = []
    for tag, index, *data in rows:
        i = int(index)
        if tag == "enter":
            calls.append({"index": i, "action": actions[i], "goal": data[0],
                          "hypotheses": data[1:], "subgoals": []})
        elif tag == "subgoal":
            calls[-1]["subgoals"].append({"goal": data[0], "hypotheses": data[1:]})
        elif tag in ("return", "raise"):
            calls[-1]["outcome"] = "returned" if tag == "return" else "raised"
            if data:
                calls[-1]["diagnostic"] = data[0]
        else:
            raise ValueError(f"unknown native tactic observation {tag!r}")
    return calls


def tactic_trace(task: TaskSpec, actions: Iterable[str], *, prepared: PreparedProject,
                 cancel=None) -> dict:
    """Replay reviewed tactics on the original proposition and record native subgoals.

    The native THEN combinator supplies branch and instantiation semantics. The
    report describes tactic execution. Call verify to establish final task success.
    """
    backend = task.prover
    if (backend not in {"hol-light", "hol4"} or task.operation != "proof_completion"
            or task.environment_id != prepared.environment_id or prepared.spec.checking_profile != "strict"
            or not reviewed(task, prepared)):
        raise ValueError("expected a reviewed HOL proof task in its prepared environment")
    prepared.validate()
    validate_inputs(task, task.artifact)
    actions = tuple(actions)
    reviewed_tactics = task.proof_atoms + task.allowed_edits
    if (not actions or len(actions) > 256
            or any(not permitted(backend, a, reviewed_tactics, ()) for a in actions)):
        raise ValueError("supply a nonempty sequence of reviewed HOL tactic expressions")
    tactics = " THEN ".join(f"(observe {i} ({a}))" for i, a in enumerate(actions))
    return _run_tactics(task, prepared, tactics, actions, cancel)


def _run_tactics(task, prepared, tactics, actions, cancel, worker=None, *, timeout_s=None):
    backend = task.prover
    light = backend == "hol-light"
    resource = "hol_light/tactics.ml" if light else "hol4/tactics.sml"
    wrapper = Path(__file__).parent / resource
    instrumented = "(" + wrapper.read_text(encoding="utf-8").replace("ITPEVAL_TACTICS", tactics) + ")"
    with tempfile.TemporaryDirectory(prefix="itpeval-hol-tactics-") as tmp:
        work = Path(tmp)
        source = work / "project"
        task.artifact.materialize(source)
        slot = task.editable_regions[0]
        path = source / slot.path
        fixed = path.read_bytes()
        path.write_bytes(fixed[:slot.start] + instrumented.encode() + fixed[slot.end:])
        trace_path = work / "trace"
        env = {k: os.environ[k] for k in ("HOME", "PATH", "USER", "LANG") if k in os.environ}
        env.update(prepared.environment)
        env.update(ITPEVAL_TRACE=str(trace_path), ITPEVAL_PROJECT=str(source),
                   ITPEVAL_ENTRY=task.artifact.entrypoint)
        tools = prepared.prefix / backend / "bin"
        if light:
            # The native launcher starts in hol.ml's directory. Resolve relative
            # project imports in the workspace, where their exact sources live.
            driver = work / "run.ml"
            driver.write_text('Sys.chdir (Sys.getenv "ITPEVAL_PROJECT");;\n'
                              'load_path := Sys.getcwd () :: !load_path;;\n'
                              'loadt (Sys.getenv "ITPEVAL_ENTRY");;\n')
            cmd = [tools / "hollight-run", driver]
        else:
            entry = Path(task.artifact.entrypoint)
            if entry.parent != Path(".") or not entry.name.endswith("Script.sml"):
                raise ValueError("expected a top-level HOL4 theory script")
            cmd = [tools / "Holmake", entry.name.removesuffix("Script.sml") + "Theory.uo"]
        limits = task.budgets
        if timeout_s is not None and not 0 < timeout_s <= limits.timeout_s:
            raise ValueError("HOL tactic timeout must be positive and fit the task's wall budget")
        if worker is None:
            result = run_process(list(map(str, cmd)), cwd=source, env=env, cancel=cancel,
                                 timeout_s=limits.timeout_s if timeout_s is None else timeout_s,
                                 max_log_bytes=limits.max_log_bytes,
                                 cpu_seconds=limits.cpu_seconds, memory_bytes=limits.memory_bytes)
        else:
            result = worker._run(task, prepared, work, cancel, timeout_s=timeout_s)
        if result.outcome != "exited":
            raise HOLTraceFailure(backend, result.outcome, (result.stdout + result.stderr)[-1800:])
        try:
            if not trace_path.is_file():
                raise RuntimeError(f"{backend} native trace missing: {(result.stdout + result.stderr)[-1800:]}")
            if trace_path.stat().st_size > limits.max_log_bytes:
                raise ValueError("native tactic trace exceeds the task's output budget")
            rows = observations(trace_path)
            status, = rows.pop()
            if status not in ("returned", "raised"):
                raise ValueError("missing native tactic result")
            goals = [{"goal": row[2], "hypotheses": row[3:]} for row in rows if row[0] == "open"]
            calls = _invocations((row for row in rows if row[0] != "open"), actions)
        except (OSError, RuntimeError, ValueError, IndexError):
            if worker is not None:
                worker.close()
            raise
        return {"task_id": task.task_id, "environment_id": task.environment_id,
                "actions": list(actions), "status": status, "invocations": calls, "open_goals": goals}


@dataclass(frozen=True)
class HOLGoal(Record):
    path: tuple[int, ...]
    conclusion: str
    hypotheses: tuple[str, ...]


@dataclass(frozen=True)
class HOLProofState(Record):
    task_id: str
    environment_id: str
    source_path: str
    target: str
    goals: tuple[HOLGoal, ...]
    diagnostic: str | None = None


@dataclass(frozen=True)
class HOLTactic(Record):
    path: tuple[int, ...]
    text: str
    subgoals: int

    def __post_init__(self):
        if (not isinstance(self.path, tuple) or len(self.path) > 256
                or any(type(index) is not int or index < 0 for index in self.path)
                or type(self.subgoals) is not int or not 0 <= self.subgoals <= 256):
            raise ValueError("invalid HOL tactic tree path or subgoal count")


@dataclass(frozen=True)
class HOLProofCheckpoint(Record):
    task_id: str
    environment_id: str
    actions: tuple[HOLTactic, ...]


class HOLProofSession(_ProofSession):
    """Edit one pending goal at a time with native HOL4 or HOL Light THENL."""

    def __init__(self, task: TaskSpec, prepared: PreparedProject, *, worker=None):
        if task.prover not in {"hol4", "hol-light"} or task.operation != "proof_completion":
            raise ValueError("expected a HOL4 or HOL Light proof task")
        self.prover = task.prover
        super().__init__(task, prepared)
        if prepared.spec.checking_profile != "strict":
            raise ValueError("native HOL proof branching requires a strict project profile")
        validate_inputs(task, task.artifact)
        if worker is not None:
            from itpeval.backends.hol_light.worker import ForkedHOLLight

            if not isinstance(worker, ForkedHOLLight):
                raise TypeError("expected a ForkedHOLLight worker")
            worker._require_task(task, prepared)
        self._worker = worker
        self._separator = ", " if self.prover == "hol4" else "; "
        self._actions: dict[tuple[int, ...], HOLTactic] = {}
        self._state = None
        self._lock = RLock()

    def _check_tactic(self, text):
        approved = self.task.proof_atoms + self.task.allowed_edits
        if not isinstance(text, str) or not permitted(self.prover, text, approved, ()):
            raise ValueError("expected a reviewed HOL tactic")

    def _render(self, actions, *, observe=None, attempt=None, path=()):
        action = actions.get(path)
        if action is None and (attempt is None or attempt[0] != path):
            return "ALL_TAC"
        tactic = attempt[1] if action is None else action.text
        if observe is not None:
            index = len(observe)
            observe.append((path, tactic))
            tactic = f"(observe {index} ({tactic}))"
        if action is not None and action.subgoals:
            children = [self._render(actions, observe=observe, attempt=attempt, path=(*path, index))
                        for index in range(action.subgoals)]
            return "((" + tactic + ") THENL [" + self._separator.join(children) + "])"
        return tactic

    def _state_for(self, goals, diagnostic=None):
        return HOLProofState(self.task.task_id, self.environment_id, self.task.artifact.entrypoint,
                             self.task.targets[0], goals, diagnostic)

    def _read_tree(self, actions, cancel, attempt=None, *, timeout_s=None):
        plan = []
        native_script = self._render(actions, observe=plan, attempt=attempt)
        if self._worker is None:
            self.prepared.validate()
        trace = _run_tactics(self.task, self.prepared, native_script, [item[1] for item in plan], cancel,
                             worker=self._worker, timeout_s=timeout_s)
        counts = {}
        for call in trace["invocations"]:
            path, _ = plan[call["index"]]
            if call["outcome"] == "raised" and attempt and path == attempt[0]:
                old = self.inspect(self.handle, cancel=cancel)
                return self._state_for(old.goals, call["diagnostic"]), actions
            if call["outcome"] != "returned" or path in counts:
                raise ValueError("native HOL replay changed a previously recorded tactic outcome")
            counts[path] = len(call["subgoals"])
            if path in actions and counts[path] != actions[path].subgoals:
                raise ValueError("native HOL replay changed a previously recorded subgoal count")
        if trace["status"] != "returned" or len(counts) != len(plan):
            raise ValueError("native HOL trace did not replay the complete tactic tree")
        if attempt:
            path, tactic = attempt
            actions = {**actions, path: HOLTactic(path, tactic, counts[path])}
        paths = self._pending_paths(actions)
        if len(paths) != len(trace["open_goals"]):
            raise ValueError("native HOL open goals differ from the recorded tactic tree")
        goals = tuple(HOLGoal(path, goal["goal"], tuple(goal["hypotheses"]))
                      for path, goal in zip(paths, trace["open_goals"]))
        return self._state_for(goals), actions

    def _pending_paths(self, actions, path=()):
        action = actions.get(path)
        if action is None:
            return [path]
        return [leaf for index in range(action.subgoals)
                for leaf in self._pending_paths(actions, (*path, index))]

    def inspect(self, handle, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self._state is None:
                self._state, _ = self._read_tree(self._actions, cancel)
            return self._state

    def step(self, handle, path, tactic, *, cancel=None, timeout_s=None):
        with self._lock:
            self.require(handle)
            self._check_tactic(tactic)
            if (not isinstance(path, tuple) or any(type(index) is not int for index in path)
                    or path not in self._pending_paths(self._actions) or len(self._actions) >= 256):
                raise ValueError("expected a current pending HOL goal path")
            state, actions = self._read_tree(self._actions, cancel, attempt=(path, tactic), timeout_s=timeout_s)
            if state.diagnostic is None:
                self._commit(actions, state)
            return self.handle, state

    def _commit(self, actions, state):
        self._actions, self._state = actions, state
        self.candidate = self._render(actions) if not state.goals else None
        self.revision = len(actions)

    def reset(self):
        with self._lock:
            self._actions = {}
            self._state = None
            return super().reset()

    def fork(self, handle):
        with self._lock:
            self.require(handle)
            child = HOLProofSession(self.task, self.prepared, worker=self._worker)
            if self._state is not None:
                child._commit(dict(self._actions), self._state)
            return child

    def checkpoint(self, handle):
        with self._lock:
            self.require(handle)
            return HOLProofCheckpoint(self.task.task_id, self.environment_id, tuple(self._actions.values()))

    def finalize(self, handle, **options):
        with self._lock:
            return super().finalize(handle, **options)

    @classmethod
    def from_checkpoint(cls, task, prepared, checkpoint: HOLProofCheckpoint, *, cancel=None, worker=None):
        """Recreate and check the recorded tactic tree in a fresh native process."""
        if (checkpoint.task_id, checkpoint.environment_id) != (task.task_id, prepared.environment_id):
            raise ValueError("HOL proof checkpoint belongs to another task or environment")
        if len(checkpoint.actions) > 256:
            raise ValueError("HOL proof checkpoint exceeds the supported tactic count")
        session = cls(task, prepared, worker=worker)
        actions = {}
        for action in checkpoint.actions:
            session._check_tactic(action.text)
            if action.path not in session._pending_paths(actions):
                raise ValueError("HOL proof checkpoint refers to a goal that was not pending")
            actions[action.path] = action
        state, actions = session._read_tree(actions, cancel)
        session._commit(actions, state)
        return session
