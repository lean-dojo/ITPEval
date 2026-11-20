"""Search an explicit ground Horn problem and replay its proof in Rocq."""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from uuid import uuid4

from itpeval.core.records import Record
from itpeval.core.types import Artifact, Budgets, TaskSpec
from itpeval.environments import PreparedProject
from itpeval.runtime.process import run_process
from itpeval.verification.fragments import permitted

from .ground import (HornEvidence, HornHypothesis, HornProblem, fresh_fact_prefix, ground_slot,
                     horn_budgets, run_ground_horn)
from .search import PreparedSolver, native_environment


_PROBE = Path(__file__).resolve().parents[1] / "extraction/native/rocq_horn.v"


@dataclass(frozen=True)
class RocqHornHypothesis(HornHypothesis):
    """A named Rocq hypothesis with the type `antecedent_1 -> ... -> consequent`."""

    language = "Rocq"
    term_keywords = frozenset({"_", "as", "else", "end", "fix", "for", "forall", "fun", "if", "in",
                               "let", "ltac", "ltac2", "match", "return", "then", "where", "with"})


@dataclass(frozen=True)
class RocqHornProblem(HornProblem):
    """Explicit Rocq propositions and premises for ground Horn proof search."""

    hypotheses: tuple[RocqHornHypothesis, ...]
    hypothesis_type = RocqHornHypothesis


@dataclass(frozen=True)
class RocqHornObservation(Record):
    """Elaborated local scope at the prepared slot in a live RocqIDE state."""

    task_id: str
    environment_id: str
    artifact_id: str
    source_path: str
    slot_byte_offset: int
    goal: str | None
    focused_goals: int
    problem: RocqHornProblem | None
    skipped_propositions: tuple[str, ...]
    reason: str | None
    probe_sha256: str
    budgets: Budgets
    duration_ms: int
    prefix: tuple[str, ...] = ()

    def to_dict(self) -> dict:
        data = super().to_dict()
        if not self.prefix:
            data.pop("prefix")
        return data


@dataclass(frozen=True)
class RocqHornEvidence(HornEvidence):
    """External proof search and the verdict of the independent Rocq replay."""

    problem: RocqHornProblem
    observation: RocqHornObservation | None = None

    def to_dict(self) -> dict:
        data = super().to_dict()
        if self.observation is None:
            data.pop("observation")
        return data


def _parse_observation(messages: list[str]) -> tuple[str, RocqHornProblem | None, tuple[str, ...]]:
    if not messages or messages[-1] != "end state":
        raise ValueError("RocqIDE did not return a complete Horn observation")
    goal = conclusion = None
    hypotheses = []
    skipped = []
    for message in messages[:-1]:
        field, _, value = message.partition(" ")
        if field == "goal" and goal is None:
            goal = value.strip()
        elif field == "conclusion" and conclusion is None:
            conclusion = value
        elif field == "skipped":
            skipped.append(value)
        elif field == "hypothesis":
            name, consequent, *antecedents = value.split("|")
            try:
                hypotheses.append(RocqHornHypothesis(name, tuple(antecedents), consequent))
            except ValueError:
                skipped.append(name)
        else:
            raise ValueError("unexpected native Horn observation field")
    if goal is None:
        raise ValueError("RocqIDE did not report the observed goal")
    problem = None
    if conclusion is not None and RocqHornHypothesis.is_atom(conclusion):
        problem = RocqHornProblem(conclusion, tuple(hypotheses))
    return goal, problem, tuple(skipped)


def _validate_prefix(task: TaskSpec, prefix: tuple[str, ...]) -> None:
    if not isinstance(prefix, tuple):
        raise ValueError("a Rocq proof prefix must be a tuple of reviewed commands")
    for index, command in enumerate(prefix):
        if not isinstance(command, str) or not command.endswith("."):
            raise ValueError("expected a reviewed Rocq prefix command ending in a period")
        if (not permitted("rocq", command, task.allowed_edits, task.proof_atoms)
                and not permitted("rocq", "\n".join(prefix[:index + 1]), task.allowed_edits, task.proof_atoms)):
            raise ValueError(f"Rocq prefix command {index + 1} is outside the task policy")


def observe_rocq_horn(task: TaskSpec, *, prepared: PreparedProject, prefix: tuple[str, ...] = (),
                      timeout_s: float | None = None, cancel: Event | None = None) -> RocqHornObservation:
    """Read one focused elaborated goal after the reviewed commands at the proof slot."""
    slot, _ = ground_slot(task, prepared, "rocq", "Rocq")
    _validate_prefix(task, prefix)
    if task.dependency_sources:
        raise ValueError("automatic Rocq Horn discovery requires prebuilt imports")
    budgets = horn_budgets(task.budgets, timeout_s)
    binary_dir = prepared.prefix / "rocq/bin"
    rocq = binary_dir / "rocq"
    ide = binary_dir / "coqidetop"
    if not ide.is_file():
        ide = rocq.resolve().with_name("coqidetop")
    if not ide.is_file():
        raise FileNotFoundError("automatic Rocq Horn discovery requires the installed coqidetop executable")
    ide = ide.resolve(strict=True)
    probe = _PROBE.read_bytes()
    files = {item.path: item.data for item in task.artifact.files}
    source = files[slot.path]
    files[slot.path] = source[:slot.start] + b"idtac.\n"
    artifact = Artifact.from_files(task.artifact.entrypoint, files)

    with TemporaryDirectory(prefix="itpeval-rocq-horn-state-") as temp:
        base = Path(temp)
        home = base / "home"
        home.mkdir()
        root = base / "source"
        artifact.materialize(root)
        probe_path = base / "probe/HornProbe.v"
        probe_path.parent.mkdir()
        probe_path.write_bytes(probe)
        request = base / "request.json"
        flags = [option for name, path in prepared.library_paths for option in ("-Q", str(path), name)]
        request.write_text(json.dumps({"entrypoint": slot.path, "slot": slot.start,
                                       "prefix": prefix, "timing": str(base / "timing"), "flags": flags,
                                       "namespace": "ITPEvalProbe" + uuid4().hex, "probe": str(probe_path),
                                       "rocq": str(rocq), "ide": str(ide)}), encoding="utf-8")
        worker = Path(__file__).with_name("_rocq_state.py")
        result = run_process([sys.executable, "-B", str(worker), str(request)], cwd=root,
                             env=native_environment(home), timeout_s=budgets.timeout_s, cpu_seconds=budgets.cpu_seconds,
                             memory_bytes=budgets.memory_bytes, max_log_bytes=budgets.max_log_bytes, cancel=cancel)
    if result.outcome != "exited" or result.returncode or result.truncated:
        diagnostic = (result.stderr or result.stdout)[-1500:].strip()
        raise ValueError(f"Rocq could not observe the proof slot ({result.outcome}, exit {result.returncode}): {diagnostic}")
    raw = json.loads(result.stdout)
    goal = problem = None
    skipped = ()
    reason = raw.get("reason")
    if reason is None:
        goal, problem, skipped = _parse_observation(raw["messages"])
        if problem is None:
            reason = "outside_ground_fragment"
    return RocqHornObservation(task.task_id, task.environment_id, task.artifact.artifact_id, slot.path, slot.start,
                               goal, raw.get("focused_goals", 0), problem, skipped, reason,
                               hashlib.sha256(probe).hexdigest(), budgets, result.duration_ms, prefix)


def _assignments(steps: tuple[HornHypothesis, ...]) -> list[tuple[str, str, str]]:
    prefix = fresh_fact_prefix(steps)
    bindings = {}
    assignments = []
    for step in steps:
        conclusion = step.consequent
        if step.antecedents:
            implication = " -> ".join((*step.antecedents, conclusion))
            args = " ".join(bindings[atom] for atom in step.antecedents)
            term = f"(({step.name} : {implication}) {args})"
        else:
            term = step.name
        name = f"{prefix}{len(bindings)}"
        assignments.append((name, conclusion, term))
        bindings[conclusion] = name
    return assignments


def _candidate(steps: tuple[HornHypothesis, ...], indent: str) -> str:
    assignments = _assignments(steps)
    lines = []
    for name, conclusion, term in assignments:
        lines.extend((f"assert ({name} : ({conclusion} : Prop)) by", f"  exact {term}."))
    lines.append(f"exact {assignments[-1][0]}.")
    return ("\n" + indent).join(lines)


def _candidate_suffix(steps: tuple[HornHypothesis, ...], indent: str) -> str:
    # A sequence of Gallina let bindings is one RocqIDE command.
    assignments = _assignments(steps)
    lines = [f"let {name} : ({conclusion} : Prop) := {term} in" for name, conclusion, term in assignments]
    lines.append(assignments[-1][0])
    return "exact (" + ("\n" + indent + "  ").join(lines) + ")."


def run_rocq_horn_search(task: TaskSpec, problem: RocqHornProblem | None = None, *, prepared: PreparedProject,
                         prefix: tuple[str, ...] = (), as_action: bool = False,
                         solver: PreparedSolver | None = None, search_timeout_s: float | None = None,
                         cancel: Event | None = None) -> RocqHornEvidence:
    """Find a proof suffix after reviewed commands and independently replay the complete proof."""
    observation = None
    if problem is None:
        observation = observe_rocq_horn(task, prepared=prepared, prefix=prefix,
                                        timeout_s=search_timeout_s, cancel=cancel)
        problem = observation.problem
        if problem is None:
            raise ValueError(f"Rocq found no supported local Horn problem: {observation.goal or observation.reason}")
    else:
        if not isinstance(problem, RocqHornProblem):
            raise TypeError("expected a RocqHornProblem")
        _validate_prefix(task, prefix)
    evidence = run_ground_horn(task, problem, prepared=prepared, prover="rocq", evidence_type=RocqHornEvidence,
                               render=_candidate, solver=solver, search_timeout_s=search_timeout_s, cancel=cancel,
                               prefix=prefix, as_action=as_action, render_suffix=_candidate_suffix)
    return replace(evidence, observation=observation)
