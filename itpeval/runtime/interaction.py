"""Native goal observations and checked trace replay for capability-aware agents."""
from __future__ import annotations

from collections.abc import Iterable
from copy import deepcopy
import hashlib
import json
import os
from dataclasses import dataclass
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory
from threading import RLock
from typing import Literal
from uuid import uuid4

from itpeval.backends.lean4._goals import proof_error
from itpeval.backends.registry import ROOT
from itpeval.core.records import Record
from itpeval.core.types import Artifact
from itpeval.runtime.process import run_process
from itpeval.runtime.sessions import StateHandle
from itpeval.verification.policies import assemble, reviewed
from itpeval.verification.service import verify


class _Revisions:
    def __init__(self, environment_id, kind):
        self.environment_id, self.kind = environment_id, kind
        self.session_id = uuid4().hex
        self.generation = self.revision = 0

    @property
    def handle(self):
        return StateHandle(self.environment_id, self.session_id, self.kind, self.generation, self.revision)

    def require(self, handle):
        if handle != self.handle:
            raise ValueError("stale or foreign interaction handle")

    def reset(self):
        self.generation += 1
        self.revision = 0
        return self.handle


class _ProofSession(_Revisions):
    prover: str

    def __init__(self, task, prepared):
        super().__init__(prepared.environment_id, self.prover)
        if (prepared.spec.prover != self.prover or task.prover != self.prover or
                task.environment_id != self.environment_id or not reviewed(task, prepared)):
            raise ValueError("task is outside this backend's reviewed completion profile")
        if prepared.spec.options or task.dependency_sources:
            raise ValueError("native interaction currently requires default options and prebuilt imports")
        self.task, self.prepared, self.candidate = task, prepared, None

    def reset(self):
        self.candidate = None
        return super().reset()

    def finalize(self, handle, **options):
        self.require(handle)
        return verify(self.task, self.candidate, prepared=self.prepared, **options)

    def _run(self, command, root, cancel, input_file=None, *, timeout_s=None):
        self.prepared.validate()
        env = {k: os.environ[k] for k in ("HOME", "PATH", "LANG", "LC_ALL", "USER") if k in os.environ}
        env.update(self.prepared.environment)
        if self.prepared.library_paths and self.prover == "lean4":
            env["LEAN_PATH"] = os.pathsep.join(str(p) for _, p in self.prepared.library_paths)
        budgets = self.task.budgets
        wall_timeout = budgets.timeout_s if timeout_s is None else min(timeout_s, budgets.timeout_s)
        result = run_process(command, cwd=root, env=env, timeout_s=wall_timeout,
                             memory_bytes=budgets.memory_bytes, cpu_seconds=budgets.cpu_seconds,
                             max_log_bytes=budgets.max_log_bytes, cancel=cancel, stdin_path=input_file)
        if result.outcome != "exited" or result.returncode or result.truncated:
            raise RuntimeError(f"interaction failed ({result.outcome}, rc={result.returncode}): "
                               + result.stderr[-2000:])
        return result.stdout

    def _editor_source(self, insertion):
        # Only internal placeholders use this method. Submitted text must first
        # pass assemble(), which enforces the reviewed proof fragment grammar.
        region = self.task.editable_regions[0]
        files = {f.path: f.data for f in self.task.artifact.files}
        src = files[region.path]
        files[region.path] = src[:region.start] + insertion.encode() + src[region.end:]
        return Artifact.from_files(self.task.artifact.entrypoint, files)


class LeanTacticSession(_ProofSession):
    """Inspect native Lean goals and replay checked tactic revisions."""
    prover = "lean4"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        self._closed = False
        self._state = None
        self._lock = RLock()

    def _revisions(self, candidates, cancel, *, stop_on_refusal=False):
        region = self.task.editable_regions[0]
        revisions = []
        for candidate in candidates:
            source = self._editor_source(candidate)
            entry = next(f for f in source.files if f.path == region.path)
            text = entry.data.decode()
            before = entry.data[:region.start + len(candidate.encode())].decode()
            line = before.rsplit("\n", 1)[-1]
            position = {"line": before.count("\n"), "character": len(line.encode("utf-16-le")) // 2}
            revisions.append({"text": text, "position": position})
        with TemporaryDirectory() as tmp:
            work = Path(tmp)
            root = work / "source"
            self.task.artifact.materialize(root)
            inputs = work / "requests.json"
            inputs.write_text(json.dumps({"entrypoint": self.task.artifact.entrypoint, "revisions": revisions,
                                          "stop_on_refusal": stop_on_refusal}),
                              encoding="utf-8")
            raw = self._run([sys.executable, str(ROOT / "backends/lean4/_goals.py"),
                             str(self.prepared.prefix / "lean4/bin/lean"), str(root), str(inputs)], root, cancel)
        records = json.loads(raw)
        if not stop_on_refusal and (len(records) != len(revisions) or
                any(row["goal"] is None and proof_error(row) is None for row in records)):
            raise ValueError("Lean did not locate a tactic state at the specified proof slot")
        return records

    def _append_tactic(self, prefix, tactic):
        candidate = prefix + " <;> " + tactic if prefix else tactic
        assemble(self.task, candidate)
        return candidate

    def inspect(self, handle, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self._state is None:
                self._state = self._revisions([self.candidate or "skip"], cancel)[0]
            else:
                self.prepared.validate()
                if cancel is not None and cancel.is_set():
                    raise RuntimeError("Lean inspection cancelled")
            return deepcopy(self._state)

    def fork(self, handle):
        """Copy the committed source revision and its last observation."""
        with self._lock:
            self.require(handle)
            child = LeanTacticSession(self.task, self.prepared)
            child.candidate, child._closed, child.revision = self.candidate, self._closed, self.revision
            child._state = deepcopy(self._state)
            return child

    def step(self, handle, tactic, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self._closed:
                raise ValueError("the Lean proof has already finished")
            candidate = self._append_tactic(self.candidate, tactic)
            before, after = self._revisions([self.candidate or "skip", candidate], cancel)
            if before["goal"] is None or proof_error(before) is not None:
                raise ValueError("Lean could not restore the current tactic state")
            if proof_error(after) is None:
                self.candidate = candidate
                self._closed = not after["goal"]["goals"]
                # inspect opens the current document as version one.
                self._state = deepcopy(dict(after, version=1))
                self.revision += 1
            return self.handle, {"before": before, "after": after}

    def replay_prefix(self, handle, actions: Iterable[str], *, cancel=None) -> tuple[dict, ...]:
        """Restore an unused session in one Lean language-server transaction.

        Return the initial observation followed by the committed observations.
        Any refused action leaves the session unchanged.
        """
        with self._lock:
            self.require(handle)
            if self.revision:
                raise ValueError("Lean replay_prefix requires an unused proof session")
            candidates = ["skip"]
            candidate = None
            for action in actions:
                candidate = self._append_tactic(candidate, action)
                candidates.append(candidate)
            rows = self._revisions(candidates, cancel, stop_on_refusal=True)
            observed = []
            for index, row in enumerate(rows):
                error = proof_error(row)
                if error is not None or row["goal"] is None:
                    where = f"replay step {index}" if index else "the initial proof state"
                    raise ValueError(f"Lean refused {where}: {error or 'no tactic state'}")
                if index < len(candidates) - 1 and not row["goal"]["goals"]:
                    raise ValueError(f"cannot replay step {index + 1}: the Lean proof has already finished")
                # The version belongs to the LSP transaction. Match inspect's
                # first document version and step's second document version.
                observed.append(dict(row, version=2 if index else 1))
            if len(observed) != len(candidates):
                raise ValueError("Lean returned an incomplete proof prefix")
            if cancel is not None and cancel.is_set():
                raise RuntimeError("Lean proof replay cancelled")
            self.candidate = candidate
            self._closed = not observed[-1]["goal"]["goals"]
            self._state = deepcopy(dict(observed[-1], version=1))
            self.revision = len(observed) - 1
            return tuple(observed)

    def reset(self):
        with self._lock:
            self._closed = False
            self._state = None
            return super().reset()

    def finalize(self, handle, **options):
        with self._lock:
            return super().finalize(handle, **options)


@dataclass(frozen=True)
class AgdaBinding(Record):
    name: str
    term: str
    reified_name: str
    in_scope: bool


@dataclass(frozen=True)
class AgdaLocation(Record):
    line: int
    column: int
    character: int


@dataclass(frozen=True)
class AgdaRange(Record):
    start: AgdaLocation
    end: AgdaLocation


@dataclass(frozen=True)
class AgdaGoalContext(Record):
    task_id: str
    environment_id: str
    source_path: str
    target: str
    interaction_id: int
    expected_type: str
    bindings: tuple[AgdaBinding, ...]
    source_range: tuple[AgdaRange, ...]


@dataclass(frozen=True)
class AgdaAutoDiagnostic(Record):
    kind: Literal["auto", "warning", "error", "incomplete"]
    message: str


@dataclass(frozen=True)
class AgdaAutoResult(Record):
    """The native Auto response for one reviewed, typed interaction point."""

    status: Literal["candidate", "no_result", "error"]
    goal: AgdaGoalContext
    candidate: str | None
    timeout_s: float
    hints: tuple[str, ...]
    diagnostics: tuple[AgdaAutoDiagnostic, ...]


_AGDA_DELIMITER = re.compile(r"^\s*=\s+")


def agda_term_candidate(task, term: str) -> str:
    """Render a term using an exact reviewed fragment when available."""
    edits = task.allowed_edits
    if not edits or not _AGDA_DELIMITER.match(edits[0]):
        return term
    prefixes = {match[0] for edit in edits if (match := _AGDA_DELIMITER.match(edit))}
    ordered = sorted(prefixes, key=lambda prefix: (prefix != "= ", len(prefix), prefix))
    for prefix in ordered:
        candidate = prefix + term
        if candidate in edits:
            return candidate
    return ordered[0] + term


def agda_candidate_term(candidate: str) -> str:
    """Read a term from the exact Agda fragment used in a proof candidate."""
    return _AGDA_DELIMITER.sub("", candidate, count=1)


_AGDA_GOAL_CONTEXT = 'Cmd_goal_type_context Normalised 0 noRange ""'


def _agda_auto_diagnostics(events):
    diagnostics = []
    for event in events:
        if event["kind"] != "DisplayInfo":
            continue
        info = event["info"]
        if info["kind"] == "Auto":
            diagnostics.append(AgdaAutoDiagnostic("auto", info["info"]))
        if info["kind"] == "Error":
            diagnostics.append(AgdaAutoDiagnostic("error", info["error"]["message"]))
        diagnostics.extend(AgdaAutoDiagnostic("warning", warning["message"]) for warning in info.get("warnings", ()))
        diagnostics.extend(AgdaAutoDiagnostic("error", error["message"]) for error in info.get("errors", ()))
    return tuple(dict.fromkeys(diagnostics))


class AgdaHoleSession(_ProofSession):
    """Inspect, solve, refine or split a reviewed Agda interaction point."""
    prover = "agda"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        self._lock = RLock()

    @property
    def _prefix(self):
        return agda_term_candidate(self.task, "")

    def _commands(self, command, cancel, *, observe_context=False, timeout_s=None):
        with TemporaryDirectory() as tmp:
            work = Path(tmp)
            root = work / "source"
            self._editor_source(self._prefix + "{! !}").materialize(root)
            path = json.dumps(str(root / self.task.artifact.entrypoint))
            input_file = work / "interaction-commands"
            actions = [f"Cmd_load {path} []", "Cmd_metas AsIs"]
            if observe_context:
                actions.append(_AGDA_GOAL_CONTEXT)
            if command:
                actions.extend((command, "Cmd_metas AsIs"))
            input_file.write_text("".join(f"IOTCM {path} None Direct ({action})\n" for action in actions),
                                  encoding="utf-8")
            argv = [str(self.prepared.prefix / "agda/bin/agda"), "--no-libraries", "--no-default-libraries", "--no-write-interfaces", "-i", str(root)]
            for _, library in self.prepared.library_paths:
                argv += ["-i", str(library)]
            raw = self._run([*argv, "--interaction-json"], root, cancel, input_file, timeout_s=timeout_s)
        events = [json.loads(data) for line in raw.splitlines()
                  if (data := line.removeprefix("JSON> ").strip())]
        points = next((event["interactionPoints"] for event in events if event["kind"] == "InteractionPoints"), [])
        slot = self.task.editable_regions[0]
        source = next(file.data for file in self.task.artifact.files if file.path == slot.path)
        location = len(source[:slot.start].decode() + self._prefix) + 1
        if (len(points) != 1 or points[0]["id"] != 0 or not points[0]["range"]
                or points[0]["range"][0]["start"]["pos"] != location):
            raise ValueError("Agda did not report a single interaction point at the prepared proof slot")
        return events

    @staticmethod
    def _filled(events):
        actions = [e["interactionPoint"]["id"] for e in events if e["kind"] == "GiveAction"]
        points = [e["interactionPoints"] for e in events if e["kind"] == "InteractionPoints"]
        info = [e["info"] for e in events if e["kind"] == "DisplayInfo"]
        summaries = [row for row in info if row["kind"] == "AllGoalsWarnings"]
        return (actions == [0] and bool(points) and not points[-1] and bool(summaries)
                and not any(row["kind"] == "Error" for row in info)
                and not any(summaries[-1].get(key) for key in ("visibleGoals", "invisibleGoals", "errors")))

    def inspect(self, handle, *, cancel=None):
        with self._lock:
            self.require(handle)
            command = None
            if self.candidate is not None:
                term = agda_candidate_term(self.candidate)
                command = "Cmd_give WithoutForce 0 noRange " + json.dumps(term, ensure_ascii=False)
            events = self._commands(command, cancel)
            if command is not None and not self._filled(events):
                raise ValueError("Agda could not restore the completed hole")
            return events

    def goal_context(self, handle, *, timeout_s: float | None = None, cancel=None) -> AgdaGoalContext:
        """Read expected type, lexical scope and native coordinates of the open hole."""
        with self._lock:
            self.require(handle)
            if self.candidate is not None:
                raise ValueError("the completion hole has already been filled")
            if timeout_s is not None and not 0 < timeout_s <= self.task.budgets.timeout_s:
                raise ValueError("context deadline must fit the task's wall budget")
            return self._goal_context(self._commands(_AGDA_GOAL_CONTEXT, cancel, timeout_s=timeout_s))

    def _goal_context(self, events):
        reports = [event["info"] for event in events
                   if event["kind"] == "DisplayInfo" and event["info"]["kind"] == "GoalSpecific"
                   and event["info"]["goalInfo"]["kind"] == "GoalType"]
        if len(reports) != 1 or reports[0]["interactionPoint"]["id"] != 0:
            raise ValueError("Agda did not identify a type for the prepared proof slot")
        report = reports[0]
        goal, point = report["goalInfo"], report["interactionPoint"]
        bindings = tuple(AgdaBinding(item["originalName"], item["binding"], item["reifiedName"], item["inScope"])
                         for item in goal["entries"])

        def location(coords):
            return AgdaLocation(coords["line"], coords["col"], coords["pos"])

        ranges = tuple(AgdaRange(location(span["start"]), location(span["end"])) for span in point["range"])
        return AgdaGoalContext(self.task.task_id, self.environment_id, self.task.artifact.entrypoint,
                               self.task.targets[0], point["id"], goal["type"], bindings, ranges)

    def auto(self, handle, *, timeout_s: float = 1.0, hints: tuple[str, ...] = (), cancel=None) -> AgdaAutoResult:
        """Ask Agda Auto for one term in a separate interaction transaction.

        The search budget is in seconds, with millisecond resolution. Submit
        the returned term through ``give`` to apply the task's proof policy.
        """
        with self._lock:
            self.require(handle)
            if self.candidate is not None:
                raise ValueError("the completion hole has already been filled")
            if type(timeout_s) not in (int, float) or not 0.001 <= timeout_s < float("inf"):
                raise ValueError("Agda Auto requires a finite timeout of at least one millisecond")
            if not isinstance(hints, tuple) or any(not isinstance(name, str) or not name or name.startswith("-")
                    or any(char.isspace() or not char.isprintable() for char in name) for name in hints):
                raise ValueError("Agda Auto hints must be a tuple of individual Agda names")
            # The native time parser stores the millisecond count in a machine Int.
            max_seconds = sys.maxsize // 1000
            milliseconds = max(1, int(min(timeout_s, self.task.budgets.timeout_s, max_seconds) * 1000))
            arguments = " ".join(("-t", f"{milliseconds}ms", *hints))
            command = "Cmd_autoOne AsIs 0 noRange " + json.dumps(arguments, ensure_ascii=False)
            events = self._commands(command, cancel, observe_context=True)
            goal = self._goal_context(events)
            diagnostics = _agda_auto_diagnostics(events)
            action = next((event for event in events if event["kind"] == "GiveAction"), None)
            if action is not None:
                term = action["giveResult"].get("str")
                if isinstance(term, str) and term.strip() and self._filled(events):
                    return AgdaAutoResult("candidate", goal, term, milliseconds / 1000, hints, diagnostics)
                diagnostics += (AgdaAutoDiagnostic("incomplete", "Agda Auto did not return a fully solved term"),)
            elif AgdaAutoDiagnostic("auto", "No solution found") in diagnostics and not any(
                    item.kind == "error" for item in diagnostics):
                return AgdaAutoResult("no_result", goal, None, milliseconds / 1000, hints, diagnostics)
            if not any(item.kind in ("auto", "error", "incomplete") for item in diagnostics):
                raise ValueError("Agda did not report an Auto result for the prepared proof slot")
            return AgdaAutoResult("error", goal, None, milliseconds / 1000, hints, diagnostics)

    def give(self, handle, term, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self.candidate is not None:
                raise ValueError("the completion hole has already been filled")
            candidate = agda_term_candidate(self.task, term)
            assemble(self.task, candidate)
            events = self._commands("Cmd_give WithoutForce 0 noRange " + json.dumps(term, ensure_ascii=False), cancel)
            if self._filled(events):
                self.candidate = candidate
                self.revision += 1
            return self.handle, events

    def case_split(self, handle, variable, *, cancel=None):
        with self._lock:
            self.require(handle)
            if self.candidate is not None or not re.fullmatch(r"[\w'-]+", variable):
                raise ValueError("case split requires an open hole and a local variable name")
            events = self._commands("Cmd_make_case 0 noRange " + json.dumps(variable, ensure_ascii=False), cancel)
            return next((event["clauses"] for event in events if event["kind"] == "MakeCase"), [])

    def reset(self):
        with self._lock:
            return super().reset()

    def fork(self, handle):
        """Copy the hole revision for a speculative native action."""
        with self._lock:
            self.require(handle)
            child = type(self)(self.task, self.prepared)
            child.candidate, child.revision = self.candidate, self.revision
            return child

    def finalize(self, handle, **options):
        with self._lock:
            return super().finalize(handle, **options)


class MetamathStackReplay(_Revisions):
    """Step through the stack operations of an already verified Metamath assertion."""
    def __init__(self, prepared, bundle, declaration_id):
        super().__init__(prepared.environment_id, "metamath_verified_stack")
        bundle = Path(bundle)
        report = json.loads((bundle / "report.json").read_text())
        if (report["environment_id"] != self.environment_id or report["prover"] != "metamath"
                or report["failed"] or prepared.spec.prover != "metamath"):
            raise ValueError("expected a verified Metamath extraction bundle for this environment")
        prepared.validate()
        key = report["structures"][declaration_id]
        if not re.fullmatch(r"[0-9a-f]{64}", key):
            raise ValueError("invalid trace hash")
        raw = (bundle / "blobs" / key[:2] / key[2:]).read_bytes()
        if hashlib.sha256(raw).hexdigest() != key:
            raise ValueError("damaged Metamath stack trace")
        self.transitions = tuple(json.loads(raw)["transitions"])

    def step(self, handle):
        self.require(handle)
        if self.revision == len(self.transitions):
            raise StopIteration
        event = self.transitions[self.revision]
        self.revision += 1
        return self.handle, event
