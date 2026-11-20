"""Shared TPTP search and certificate-guided reconstruction for ground Horn clauses."""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event
from typing import ClassVar, TypeVar

from itpeval.core.records import Record
from itpeval.core.types import Budgets, EditableRegion, TaskSpec, VerificationEvidence
from itpeval.environments import PreparedProject
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import reviewed, validate_inputs
from itpeval.verification.service import verify

from .search import PreparedSolver, SearchEvidence, prepare_solver


_NAME = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
_ATOM = re.compile(rf"{_NAME}(?: {_NAME})*")
_ORIGIN = re.compile(r"file\('input-0\.p',\s*(?P<quote>'?)(?P<label>premise_\d+|goal)(?P=quote)\)")


@dataclass(frozen=True)
class HornHypothesis(Record):
    name: str
    antecedents: tuple[str, ...]
    consequent: str

    language: ClassVar[str]
    term_keywords: ClassVar[frozenset[str]]

    @classmethod
    def is_atom(cls, text: str) -> bool:
        return bool(_ATOM.fullmatch(text)) and cls.term_keywords.isdisjoint(text.split())

    def __post_init__(self):
        if not re.fullmatch(_NAME, self.name) or self.name in self.term_keywords:
            raise ValueError(f"Horn hypothesis names must be {self.language} identifiers")
        if any(not self.is_atom(atom) for atom in (*self.antecedents, self.consequent)):
            raise ValueError(f"Horn atoms must be {self.language} identifiers or flat applications of identifiers")


@dataclass(frozen=True)
class HornProblem(Record):
    conclusion: str
    hypotheses: tuple[HornHypothesis, ...]

    hypothesis_type: ClassVar[type[HornHypothesis]]

    def __post_init__(self):
        dialect = self.hypothesis_type
        if not dialect.is_atom(self.conclusion):
            raise ValueError(f"the Horn conclusion must be a {dialect.language} identifier or flat application")
        if not all(isinstance(hypothesis, dialect) for hypothesis in self.hypotheses):
            raise ValueError(f"expected {dialect.language} Horn hypotheses")
        if len({hypothesis.name for hypothesis in self.hypotheses}) != len(self.hypotheses):
            raise ValueError("Horn hypotheses must have distinct names")

    def to_tptp(self) -> str:
        """Abstract each ground proposition as a distinct TPTP atom."""
        atoms = {self.conclusion}
        for hypothesis in self.hypotheses:
            atoms.update((*hypothesis.antecedents, hypothesis.consequent))
        labels = {atom: f"p{index}" for index, atom in enumerate(sorted(atoms))}
        lines = []
        for index, hypothesis in enumerate(self.hypotheses):
            consequent = labels[hypothesis.consequent]
            antecedent = " & ".join(labels[atom] for atom in hypothesis.antecedents)
            body = f"(({antecedent}) => {consequent})" if antecedent else consequent
            lines.append(f"fof(premise_{index}, axiom, {body}).")
        lines.append(f"fof(goal, conjecture, {labels[self.conclusion]}).")
        return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class HornEvidence(Record):
    task_id: str
    environment_id: str
    target: str
    problem: HornProblem
    tptp: str
    search: SearchEvidence
    certificate_hypotheses: tuple[str, ...] = ()
    reconstructed_hypotheses: tuple[str, ...] = ()
    candidate: str | None = None
    replay_outcome: str = "not_attempted"
    replay: VerificationEvidence | None = None
    suffix: str | None = None

    def to_dict(self) -> dict:
        data = super().to_dict()
        if self.suffix is None:
            data.pop("suffix")
        return data


def _proof_hypotheses(problem: HornProblem, certificate: str) -> tuple[HornHypothesis, ...]:
    labels = {match["label"] for match in _ORIGIN.finditer(certificate)}
    if "goal" not in labels:
        return ()
    return tuple(hypothesis for index, hypothesis in enumerate(problem.hypotheses)
                 if f"premise_{index}" in labels)


def _derive(conclusion: str, hypotheses: tuple[HornHypothesis, ...]) -> tuple[HornHypothesis, ...]:
    known = {}
    while conclusion not in known:
        previous_size = len(known)
        for hypothesis in hypotheses:
            if hypothesis.consequent not in known and all(atom in known for atom in hypothesis.antecedents):
                known[hypothesis.consequent] = hypothesis
        if previous_size == len(known):
            return ()
    # Keep only the ancestor clauses of the conclusion, in derivation order.
    uses = {conclusion}
    required = []
    for atom, hypothesis in reversed(known.items()):
        if atom in uses:
            uses.update(hypothesis.antecedents)
            required.append(hypothesis)
    return tuple(reversed(required))


def fresh_fact_prefix(steps: tuple[HornHypothesis, ...]) -> str:
    """Generate local proof bindings that leave every mapped name in scope."""
    reserved = {identifier for hypothesis in steps
                for item in (hypothesis.name, *hypothesis.antecedents, hypothesis.consequent)
                for identifier in re.split(r"[ .]", item)}
    prefix = "hornFact"
    while any(name.startswith(prefix) for name in reserved):
        prefix += "_"
    return prefix


_Evidence = TypeVar("_Evidence", bound=HornEvidence)


def ground_slot(task: TaskSpec, prepared: PreparedProject, prover: str, language: str) -> tuple[EditableRegion, str]:
    if (task.prover != prover or prepared.spec.prover != prover or task.operation != "proof_completion"
            or not task.manifest_path or task.environment_id != prepared.environment_id
            or prepared.spec.checking_profile != "strict" or not reviewed(task, prepared)):
        raise ValueError(f"Horn search requires a reviewed {language} completion task in its locked project")
    prepared.validate()
    validate_inputs(task, task.artifact)
    slot = task.editable_regions[0]
    source = next(item.data for item in task.artifact.files if item.path == slot.path)
    indent = source[source.rfind(b"\n", 0, slot.start) + 1:slot.start].decode()
    if prover == "lean4" and (indent.strip(" ") or not indent):
        raise ValueError("Lean Horn replay requires a tactic slot on its own indented line")
    if prover == "rocq" and indent.strip(" \t"):
        raise ValueError("Rocq Horn replay requires a tactic slot on its own line")
    return slot, indent


def horn_budgets(budgets: Budgets, timeout_s: float | None) -> Budgets:
    if timeout_s is not None and not 0 < timeout_s <= budgets.timeout_s:
        raise ValueError("timeout must be positive and fit the task's wall budget")
    return replace(budgets, timeout_s=min(30, budgets.timeout_s) if timeout_s is None else timeout_s)


def run_ground_horn(task: TaskSpec, problem: HornProblem, *, prepared: PreparedProject, prover: str,
                    evidence_type: type[_Evidence], render: Callable[[tuple[HornHypothesis, ...], str], str],
                    solver: PreparedSolver | None, search_timeout_s: float | None,
                    cancel: Event | None, prefix: tuple[str, ...] = (), as_action: bool = False,
                    render_suffix: Callable[[tuple[HornHypothesis, ...], str], str] | None = None) -> _Evidence:
    search_budgets = horn_budgets(task.budgets, search_timeout_s)
    _, indent = ground_slot(task, prepared, prover, problem.hypothesis_type.language)
    scoped = bool(prefix) or as_action
    if scoped and render_suffix is None:
        raise ValueError("interactive Horn search requires a native single-action renderer")

    tptp = problem.to_tptp()
    solver = solver or prepare_solver("e", prefix=prepared.prefix)
    with TemporaryDirectory(prefix=f"itpeval-{prover}-horn-") as temp:
        source_path = Path(temp) / "horn.p"
        source_path.write_bytes(tptp.encode("ascii"))
        search = solver.solve(source_path, budgets=search_budgets, cancel=cancel)
    evidence = evidence_type(task.task_id, task.environment_id, task.targets[0], problem, tptp, search)
    if search.outcome != "theorem":
        return evidence
    hypotheses = _proof_hypotheses(problem, search.certificate or "")
    if not hypotheses:
        return replace(evidence, replay_outcome="certificate_hypotheses_unavailable")
    evidence = replace(evidence, certificate_hypotheses=tuple(hypothesis.name for hypothesis in hypotheses))
    steps = _derive(problem.conclusion, hypotheses)
    if not steps:
        return replace(evidence, replay_outcome="reconstruction_failed")
    suffix = render_suffix(steps, indent) if scoped else None
    if suffix is None:
        candidate = render(steps, indent)
    else:
        separator = " <;> " if prover == "lean4" else "\n"
        candidate = separator.join((*prefix, suffix))
    evidence = replace(evidence, candidate=candidate, suffix=suffix,
                       reconstructed_hypotheses=tuple(step.name for step in steps))
    if not permitted(task.prover, candidate, task.allowed_edits, task.proof_atoms):
        return replace(evidence, replay_outcome="outside_task_policy")
    replay = verify(task, candidate, prepared=prepared, cancel=cancel)
    outcome = "accepted" if replay.task_success else (
        "rejected" if replay.task_success is False else replay.execution_outcome)
    return replace(evidence, replay_outcome=outcome, replay=replay)
