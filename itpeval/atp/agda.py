"""Search a ground Horn abstraction of one typed Agda interaction point."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, replace
from threading import Event

from itpeval.core.records import Record
from itpeval.core.types import TaskSpec
from itpeval.environments import PreparedProject
from itpeval.runtime.interaction import AgdaGoalContext, AgdaHoleSession, agda_candidate_term, agda_term_candidate

from .ground import HornEvidence, HornHypothesis, HornProblem, fresh_fact_prefix, ground_slot, horn_budgets, run_ground_horn
from .search import PreparedSolver


@dataclass(frozen=True)
class AgdaHornHypothesis(HornHypothesis):
    """A scope-local inhabitant of an atom or a non-dependent function type."""

    language = "Agda"
    term_keywords = frozenset({"_", "abstract", "constructor", "data", "do", "field", "forall", "in", "instance",
                               "let", "module", "open", "pattern", "postulate", "private", "Prop", "quote", "record",
                               "rewrite", "Set", "Setω", "unquote", "variable", "where", "with"})


@dataclass(frozen=True)
class AgdaHornProblem(HornProblem):
    """An atomic goal and named local Agda Horn hypotheses."""

    hypotheses: tuple[AgdaHornHypothesis, ...]
    hypothesis_type = AgdaHornHypothesis


@dataclass(frozen=True)
class AgdaHornObservation(Record):
    """The native hole context and the subset representable as Horn clauses."""

    task_id: str
    environment_id: str
    artifact_id: str
    slot_byte_offset: int
    context: AgdaGoalContext
    problem: AgdaHornProblem | None
    skipped_bindings: tuple[str, ...]

    @property
    def goal(self) -> str:
        return self.context.expected_type


@dataclass(frozen=True)
class AgdaHornEvidence(HornEvidence):
    """The external proof search and independent check of its Agda term."""

    problem: AgdaHornProblem
    observation: AgdaHornObservation | None = None


def _types(context: AgdaGoalContext) -> dict[str, str]:
    names = Counter(binding.reified_name for binding in context.bindings)
    return {binding.name: " ".join(binding.term.split()) for binding in context.bindings
            if names[binding.name] == 1 and binding.name == binding.reified_name and " " not in binding.name
            and AgdaHornHypothesis.is_atom(binding.name)}


def _atom(raw: str, local_types: dict[str, str]) -> str | None:
    text = " ".join(raw.split())
    if not AgdaHornHypothesis.is_atom(text):
        return None
    head, *args = text.split()
    family = local_types.get(head)
    if family is None:
        return None
    *domains, result = map(str.strip, family.split("→"))
    if result == "Set" and len(args) == len(domains) and all(local_types.get(arg) == domain
            for arg, domain in zip(args, domains)):
        return text
    return None


def _problem(context: AgdaGoalContext) -> tuple[AgdaHornProblem | None, tuple[str, ...]]:
    local_types = _types(context)
    conclusion = _atom(context.expected_type, local_types)
    hypotheses, skipped = [], []
    for binding in context.bindings:
        native_type = local_types.get(binding.name)
        if native_type is not None and binding.in_scope and binding.name == binding.reified_name:
            clauses = tuple(_atom(part, local_types) for part in native_type.split("→"))
            if all(clause is not None for clause in clauses):
                hypotheses.append(AgdaHornHypothesis(binding.name, clauses[:-1], clauses[-1]))
                continue
        skipped.append(binding.name)
    problem = AgdaHornProblem(conclusion, tuple(hypotheses)) if conclusion is not None else None
    return problem, tuple(skipped)


def observe_agda_horn(task: TaskSpec, *, prepared: PreparedProject, timeout_s: float | None = None,
                      cancel: Event | None = None) -> AgdaHornObservation:
    """Read named types and their ground applications from an actual Agda goal."""
    slot, _ = ground_slot(task, prepared, "agda", "Agda")
    budgets = horn_budgets(task.budgets, timeout_s)
    session = AgdaHoleSession(task, prepared)
    context = session.goal_context(session.handle, timeout_s=budgets.timeout_s, cancel=cancel)
    problem, skipped = _problem(context)
    return AgdaHornObservation(task.task_id, task.environment_id, task.artifact.artifact_id, slot.start,
                               context, problem, skipped)


def _term(steps: tuple[HornHypothesis, ...]) -> str:
    prefix = fresh_fact_prefix(steps)
    bindings = {}
    definitions = []
    for step in steps[:-1]:
        name = f"{prefix}{len(definitions)}"
        value = " ".join((step.name, *(bindings[atom] for atom in step.antecedents)))
        definitions.append(f"{name} = {value}")
        bindings[step.consequent] = name
    last = steps[-1]
    result = " ".join((last.name, *(bindings[atom] for atom in last.antecedents)))
    # Share derived terms to keep the native fragment linear in proof edges.
    return "let " + "; ".join(definitions) + " in " + result if definitions else result


def _search_agda_problem(task: TaskSpec, problem: AgdaHornProblem, *, observation: AgdaHornObservation,
                         prepared: PreparedProject, solver: PreparedSolver | None = None,
                         search_timeout_s: float | None = None, cancel: Event | None = None) -> AgdaHornEvidence:
    if ((observation.task_id, observation.environment_id, observation.artifact_id) !=
            (task.task_id, task.environment_id, task.artifact.artifact_id) or observation.problem != problem):
        raise ValueError("Agda Horn observation belongs to another task or problem")
    evidence = run_ground_horn(task, problem, prepared=prepared, prover="agda", evidence_type=AgdaHornEvidence,
                               render=lambda steps, _: agda_term_candidate(task, _term(steps)), solver=solver,
                               search_timeout_s=search_timeout_s, cancel=cancel)
    term = agda_candidate_term(evidence.candidate) if evidence.candidate is not None else None
    return replace(evidence, observation=observation, suffix=term)


def run_agda_horn_search(task: TaskSpec, *, prepared: PreparedProject, solver: PreparedSolver | None = None,
                         search_timeout_s: float | None = None, cancel: Event | None = None) -> AgdaHornEvidence:
    """Search the observed Horn goal and independently check the resulting fragment."""
    observation = observe_agda_horn(task, prepared=prepared, timeout_s=search_timeout_s, cancel=cancel)
    if observation.problem is None:
        raise ValueError(f"Agda found no supported local Horn problem for goal: {observation.goal}")
    return _search_agda_problem(task, observation.problem, observation=observation, prepared=prepared,
                                solver=solver, search_timeout_s=search_timeout_s, cancel=cancel)
