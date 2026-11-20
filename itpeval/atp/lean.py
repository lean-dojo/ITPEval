"""Discover and solve ground Horn goals at a reviewed Lean tactic boundary."""

from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass, replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event

from itpeval.core.records import Record
from itpeval.core.types import Artifact, Budgets, TaskSpec
from itpeval.environments import PreparedProject
from itpeval.runtime.process import run_process
from itpeval.verification.policies import assemble

from .ground import (HornEvidence, HornHypothesis, HornProblem, fresh_fact_prefix, ground_slot,
                     horn_budgets, run_ground_horn)
from .search import PreparedSolver, native_environment


_PROBE = Path(__file__).resolve().parents[1] / "extraction/native/lean_horn.lean"
_PROBE_MARKER = "ITPEVAL_HORN_STATE "


@dataclass(frozen=True)
class LeanHornHypothesis(HornHypothesis):
    """A named Lean hypothesis with the type `antecedent₁ → … → consequent`."""

    language = "Lean"
    term_keywords = frozenset({"_", "by", "calc", "do", "else", "from", "fun", "have", "if", "let",
                               "match", "show", "then", "where", "with"})


@dataclass(frozen=True)
class LeanHornProblem(HornProblem):
    """Explicit Lean propositions and premises for ground Horn proof search."""

    hypotheses: tuple[LeanHornHypothesis, ...]
    hypothesis_type = LeanHornHypothesis


@dataclass(frozen=True)
class LeanHornObservation(Record):
    """Elaborated local scope at the slot or after a reviewed tactic prefix."""

    task_id: str
    environment_id: str
    artifact_id: str
    source_path: str
    slot_byte_offset: int
    goal: str
    problem: LeanHornProblem | None
    skipped_propositions: tuple[str, ...]
    probe_sha256: str
    budgets: Budgets
    duration_ms: int
    prefix: tuple[str, ...] = ()
    probe_byte_offset: int | None = None

    def to_dict(self) -> dict:
        data = super().to_dict()
        if not self.prefix:
            data.pop("prefix")
            data.pop("probe_byte_offset")
        return data


@dataclass(frozen=True)
class LeanHornEvidence(HornEvidence):
    """External proof search and the verdict of the independent Lean replay."""

    problem: LeanHornProblem
    observation: LeanHornObservation | None = None

    def to_dict(self) -> dict:
        data = super().to_dict()
        if self.observation is None:
            data.pop("observation")
        return data


def observe_lean_horn(task: TaskSpec, *, prepared: PreparedProject, prefix: tuple[str, ...] = (),
                      timeout_s: float | None = None, cancel: Event | None = None) -> LeanHornObservation:
    """Read one elaborated goal and its supported local clauses from the Lean frontend.

    Unsupported goals have no Horn problem. Propositions outside the fragment
    are listed separately and never submitted to the solver.
    """
    slot, indent = ground_slot(task, prepared, "lean4", "Lean")
    if prepared.spec.options or task.dependency_sources:
        raise ValueError("automatic Lean Horn discovery requires default checker options and prebuilt imports")
    budgets = horn_budgets(task.budgets, timeout_s)
    probe = _PROBE.read_bytes()
    files = {item.path: item.data for item in task.artifact.files}
    source = files[slot.path]
    if not isinstance(prefix, tuple) or any(not isinstance(tactic, str) for tactic in prefix):
        raise TypeError("expected a tuple of Lean tactics")
    committed = ""
    for tactic in prefix:
        committed = committed + " <;> " + tactic if committed else tactic
        assemble(task, committed)
    # Observe the whole pending goal list before any application of a new
    # tactic. Putting the probe under <;> would run it on each subgoal.
    composition = (committed + "\n" + indent).encode("utf-8") if prefix else b""
    probe_offset = slot.start + len(composition)
    files[slot.path] = source[:slot.start] + composition + b"skip" + source[slot.end:]
    artifact = Artifact.from_files(task.artifact.entrypoint, files)

    with TemporaryDirectory(prefix="itpeval-lean-horn-state-") as temp:
        base = Path(temp)
        root = base / "source"
        home = base / "home"
        home.mkdir()
        artifact.materialize(root)
        driver = base / "LeanHornState.lean"
        driver.write_bytes(probe)
        env = native_environment(home)
        library_path = prepared.environment.get("ITPEVAL_LEAN4_LEAN_PATH")
        if library_path:
            env["LEAN_PATH"] = os.pathsep.join((str(root), library_path))
        lean = prepared.prefix / "lean4/bin/lean"
        target = task.targets[0].rsplit(".", 1)[-1]
        result = run_process([str(lean), "--run", str(driver), slot.path, str(probe_offset), target],
                             cwd=root, env=env, timeout_s=budgets.timeout_s, cpu_seconds=budgets.cpu_seconds,
                             memory_bytes=budgets.memory_bytes, max_log_bytes=budgets.max_log_bytes, cancel=cancel)
    if result.outcome != "exited" or result.returncode or result.truncated:
        diagnostic = (result.stderr or result.stdout)[-1500:].strip()
        raise ValueError(f"Lean could not observe the proof slot ({result.outcome}, exit {result.returncode}): {diagnostic}")
    reports = [line.removeprefix(_PROBE_MARKER) for line in result.stdout.splitlines() if line.startswith(_PROBE_MARKER)]
    if len(reports) != 1:
        raise ValueError("expected one native Lean proof-slot observation")
    raw = json.loads(reports[0])
    skipped = raw["skipped_propositions"]
    hypotheses = []
    for row in raw["hypotheses"]:
        try:
            hypotheses.append(LeanHornHypothesis(row["name"], tuple(row["antecedents"]), row["consequent"]))
        except ValueError:
            skipped.append(row["name"])
    conclusion = raw["conclusion"]
    problem = None
    if conclusion is not None and LeanHornHypothesis.is_atom(conclusion):
        try:
            problem = LeanHornProblem(conclusion, tuple(hypotheses))
        except ValueError:
            # Retain the native observation when the scope cannot be mapped.
            pass
    return LeanHornObservation(task.task_id, task.environment_id, task.artifact.artifact_id, slot.path, slot.start,
                               raw["goal"], problem, tuple(skipped), hashlib.sha256(probe).hexdigest(),
                               budgets, result.duration_ms, prefix, probe_offset if prefix else None)


def _candidate(steps: tuple[HornHypothesis, ...], indent: str) -> str:
    prefix = fresh_fact_prefix(steps)
    bindings = {}
    lines = []
    for step in steps:
        conclusion = step.consequent
        if step.antecedents:
            implication = " → ".join((*step.antecedents, conclusion))
            args = " ".join(bindings[atom] for atom in step.antecedents)
            term = f"(show {implication} from {step.name}) {args}"
        else:
            term = step.name
        name = f"{prefix}{len(bindings)}"
        lines.extend((f"have {name} : ({conclusion} : Prop) :=", f"  {term}"))
        bindings[conclusion] = name
    lines.append(f"exact {bindings[steps[-1].consequent]}")
    return ("\n" + indent).join(lines)


def _suffix(steps: tuple[HornHypothesis, ...], indent: str) -> str:
    nested = indent + "  "
    return "exact (by\n" + nested + _candidate(steps, nested) + ")"


def run_horn_search(task: TaskSpec, problem: LeanHornProblem | None = None, *, prepared: PreparedProject,
                    solver: PreparedSolver | None = None, search_timeout_s: float | None = None,
                    cancel: Event | None = None, prefix: tuple[str, ...] = (),
                    as_action: bool = False) -> LeanHornEvidence:
    """Search the given Horn abstraction and check a reconstructed tactic in the original task.

    Omit the problem to discover the ground clauses after the reviewed prefix.
    Named hypotheses, arrow types, and the conclusion are checked by Lean.
    The reviewed completion manifest controls which generated scripts may run.
    """
    if not isinstance(prefix, tuple):
        raise TypeError("expected a tuple of Lean tactics")
    if problem is not None and not isinstance(problem, LeanHornProblem):
        raise TypeError("expected a LeanHornProblem")
    observation = (observe_lean_horn(task, prepared=prepared, prefix=prefix, timeout_s=search_timeout_s, cancel=cancel)
                   if problem is None or prefix or as_action else None)
    if problem is None:
        problem = observation.problem
        if problem is None:
            raise ValueError(f"Lean found no supported local Horn problem for goal: {observation.goal}")
    return _search_lean_problem(task, problem, prepared=prepared, solver=solver,
                                search_timeout_s=search_timeout_s, cancel=cancel, prefix=prefix,
                                as_action=as_action, observation=observation)


def _search_lean_problem(task, problem, *, prepared, solver, search_timeout_s, cancel, prefix, as_action, observation):
    # Callers using an observation collected in this transaction can reuse it.
    evidence = run_ground_horn(task, problem, prepared=prepared, prover="lean4", evidence_type=LeanHornEvidence,
                               render=_candidate, render_suffix=_suffix, solver=solver,
                               search_timeout_s=search_timeout_s, cancel=cancel, prefix=prefix, as_action=as_action)
    return replace(evidence, observation=observation)
