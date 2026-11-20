"""Explore alternative native proof continuations from one locked revision."""

from __future__ import annotations

from collections import deque
from copy import deepcopy
from dataclasses import dataclass

from itpeval.atp.session import NativeATPSuggestion
from itpeval.atp.strategies import _Deadline
from itpeval.core.records import Record, digest
from itpeval.learning.episodes import _compare
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import ATPProgress, NativeProofEpisode, SearchWithATP, check_native_episode
from itpeval.runtime.proof_driver import (NativeProofAction, NativeProofCheckpoint, NativeProofDriver,
                                          NativeProofFinalization, NativeProofObservation, NativeProofTransition)


@dataclass(frozen=True)
class PortfolioTrial(Record):
    parent: int | None
    outcome: str
    action: NativeProofAction | None = None
    transition: NativeProofTransition | None = None
    suggestion: NativeATPSuggestion | None = None
    finalization: NativeProofFinalization | None = None
    diagnostic: str | None = None


@dataclass(frozen=True)
class ProofPortfolio(Record):
    start: NativeProofCheckpoint
    observation: NativeProofObservation
    policy_id: str
    max_trials: int
    max_depth: int
    timeout_s: float
    outcome: str
    trials: tuple[PortfolioTrial, ...]
    winner: int | None = None

    def __post_init__(self):
        if (self.observation.state_id != self.start.state_ids[-1] or not self.policy_id
                or not 1 <= self.max_trials <= 256 or not 1 <= self.max_depth <= 256
                or len(self.trials) > self.max_trials or not 0 < self.timeout_s < float("inf")):
            raise ValueError("invalid proof portfolio identity or bounds")
        depths = []
        for index, trial in enumerate(self.trials):
            if trial.parent is None:
                depth = 1
            else:
                if not 0 <= trial.parent < index:
                    raise ValueError("a proof trial must refer to an earlier parent")
                previous = self.trials[trial.parent].transition
                if not previous or not previous.committed or previous.observation.status not in {"open", "rejected"}:
                    raise ValueError("a proof trial requires a committed, still editable parent")
                depth = depths[trial.parent] + 1
            if depth > self.max_depth or (trial.transition is not None and trial.transition.action != trial.action):
                raise ValueError("proof trial exceeds the declared depth or reports a different action")
            depths.append(depth)
        if (self.outcome == "accepted") != (self.winner is not None):
            raise ValueError("accepted proof portfolios require a winning trial")
        if self.winner is not None:
            if self.winner != len(self.trials) - 1 or self.winner < 0:
                raise ValueError("the winning trial must end the portfolio")
            winner = self.trials[self.winner]
            if (winner.finalization is None or winner.finalization.evidence.task_success is not True
                    or winner.transition is None or not winner.transition.committed
                    or winner.transition.observation.status != "ready"):
                raise ValueError("the winning branch needs a complete proof accepted by the checker")

    def winning_trials(self) -> tuple[PortfolioTrial, ...]:
        """Return the selected continuation in native action order."""
        path, index = [], self.winner
        while index is not None:
            trial = self.trials[index]
            path.append(trial)
            index = trial.parent
        return tuple(reversed(path))

    @property
    def winning_checkpoint(self) -> NativeProofCheckpoint | None:
        steps = self.winning_trials()
        if not steps:
            return None
        return NativeProofCheckpoint(self.start.task_id, self.start.environment_id,
                                     self.start.actions + tuple(step.action for step in steps),
                                     self.start.state_ids + tuple(step.transition.observation.state_id for step in steps))


def _attempt(branch, decision, parent, deadline, proof_fragment):
    suggestion = None
    action = decision if isinstance(decision, NativeProofAction) else None
    transition = None
    final = None
    try:
        if isinstance(decision, SearchWithATP):
            suggestion = branch.suggest_atp(solver=decision.solver, executable=decision.executable,
                                            timeout_s=decision.timeout_s, goal_path=decision.goal_path,
                                            max_trials=decision.max_trials, hints=decision.hints,
                                            proof_fragment=proof_fragment, cancel=deadline)
            action = suggestion.action
            if suggestion.outcome not in {"accepted", "progress"}:
                return PortfolioTrial(parent, deadline.outcome or suggestion.outcome, action, suggestion=suggestion)
            transition = branch.apply_atp(suggestion, cancel=deadline)
        else:
            transition = branch.advance(action, cancel=deadline)
        outcome = transition.observation.status
        if transition.committed and outcome == "ready":
            final = suggestion.finalization if suggestion is not None else None
            if final is None:
                if branch.task.prover == "pvs" and proof_fragment is None and len(branch.checkpoint().actions) != 1:
                    return PortfolioTrial(parent, "proof_fragment_required", action, transition, suggestion)
                final = branch.finalize(proof_fragment=proof_fragment, cancel=deadline)
            evidence = final.evidence
            outcome = ("accepted" if evidence.task_success is True else evidence.checker_outcome
                       if evidence.task_success is False else deadline.outcome or evidence.execution_outcome)
        return PortfolioTrial(parent, outcome, action, transition, suggestion, final)
    except ValueError as error:
        return PortfolioTrial(parent, deadline.outcome or "refused", action, transition, suggestion, diagnostic=str(error))
    except (OSError, RuntimeError) as error:
        return PortfolioTrial(parent, deadline.outcome or getattr(error, "outcome", "unavailable"),
                              action, transition, suggestion, diagnostic=str(error))


def search_portfolio(driver: NativeProofDriver, propose, *, policy_id: str, max_trials=32, max_depth=8,
                     timeout_s=None, proof_fragment=None, cancel=None) -> ProofPortfolio:
    """Try an ordered policy's actions breadth first on independent forks.

    `propose(task, state, history)` yields NativeProofAction or SearchWithATP
    decisions. History is the route to the current branch. The trial budget
    counts top-level decisions. If startup cannot capture a native state before
    the deadline, raise TimeoutError or InterruptedError instead of an archive.
    """
    if not isinstance(policy_id, str) or not policy_id.strip():
        raise ValueError("supply a nonempty policy identity")
    if any(type(limit) is not int or not 1 <= limit <= 256 for limit in (max_trials, max_depth)):
        raise ValueError("trial and depth limits must be integers from 1 to 256")
    timeout = min(30, driver.task.budgets.timeout_s) if timeout_s is None else timeout_s
    if not 0 < timeout <= driver.task.budgets.timeout_s:
        raise ValueError("portfolio timeout must be positive and fit the task's wall budget")
    if proof_fragment is not None and driver.task.prover != "pvs":
        raise ValueError("a separate finishing fragment is only used by PVS")
    deadline = _Deadline(timeout, cancel)
    try:
        if deadline.is_set():
            raise InterruptedError("portfolio startup was stopped")
        seed = driver.fork(cancel=deadline)
    except (OSError, RuntimeError, ValueError) as error:
        if deadline.outcome == "cancelled":
            raise InterruptedError("portfolio cancelled before capturing a native state") from error
        if deadline.outcome == "timeout":
            raise TimeoutError("portfolio timed out before capturing a native state") from error
        raise
    start = seed.checkpoint()
    if len(start.actions) + max_depth > 256:
        raise ValueError("portfolio depth exceeds the remaining native action capacity")
    initial = seed.observe()
    if initial.status not in {"open", "rejected"}:
        raise ValueError("portfolio search needs a goal or an editable document revision")
    trials = []

    def result(outcome, winner=None):
        return ProofPortfolio(start, initial, policy_id, max_trials, max_depth, timeout, outcome, tuple(trials), winner)

    frontier = deque([(seed, ())])
    seen = {digest(start.to_dict())}
    truncated = False
    while frontier:
        if deadline.is_set() or len(trials) == max_trials:
            return result(deadline.outcome or "trial_limit")
        node, route = frontier.popleft()
        parent = route[-1] if route else None
        history = tuple(deepcopy(trials[i]) for i in route)
        decisions = iter(propose(driver.task, node.observe(), history))
        while True:
            if deadline.is_set() or len(trials) == max_trials:
                return result(deadline.outcome or "trial_limit")
            try:
                decision = next(decisions)
            except StopIteration:
                break
            if deadline.is_set():
                return result(deadline.outcome)
            if not isinstance(decision, (NativeProofAction, SearchWithATP)):
                raise TypeError("portfolio policies must yield NativeProofAction or SearchWithATP decisions")
            try:
                branch = node.fork(cancel=deadline)
            except (OSError, RuntimeError) as error:
                action = decision if isinstance(decision, NativeProofAction) else None
                trials.append(PortfolioTrial(parent, deadline.outcome or getattr(error, "outcome", "unavailable"),
                                             action=action, diagnostic=str(error)))
                continue
            trial = _attempt(branch, decision, parent, deadline, proof_fragment)
            trials.append(trial)
            index = len(trials) - 1
            if trial.outcome == "accepted":
                return result("accepted", index)
            transition = trial.transition
            if transition is not None and transition.committed and transition.observation.status in {"open", "rejected"}:
                key = digest(branch.checkpoint().to_dict())
                if key in seen:
                    continue
                seen.add(key)
                if len(route) + 1 == max_depth:
                    truncated = True
                else:
                    frontier.append((branch, (*route, index)))
    return result(deadline.outcome or ("depth_limit" if truncated else "exhausted"))


def replay_portfolio(portfolio: ProofPortfolio, *, task, prepared, cancel=None,
                     **session_options) -> NativeProofEpisode:
    """Recheck the winning route and emit a sequential proof training episode."""
    if (task.task_id, prepared.environment_id) != (portfolio.start.task_id, portfolio.start.environment_id):
        raise ValueError("portfolio belongs to another task or environment")
    route = portfolio.winning_trials()
    if not route:
        raise ValueError("portfolio has no verified winning continuation")
    driver = NativeProofDriver(task, prepared, **session_options)
    initial = driver.observe(cancel=cancel)
    if initial.state_id != portfolio.start.state_ids[0]:
        raise ValueError("initial native state changed during portfolio replay")
    transitions, progress = [], []
    for action, expected in zip(portfolio.start.actions, portfolio.start.state_ids[1:]):
        step = driver.advance(action, cancel=cancel)
        if not step.committed or step.observation.state_id != expected:
            raise ValueError("saved prefix changed during portfolio replay")
        transitions.append(step)
    if driver.observe().status != portfolio.observation.status:
        raise ValueError("starting portfolio goal status changed during replay")

    for trial in route:
        if trial.suggestion is not None:
            step = driver.apply_atp(trial.suggestion, cancel=cancel)
            if trial.suggestion.outcome == "progress":
                progress.append(ATPProgress(len(transitions), trial.suggestion))
        else:
            step = driver.advance(trial.action, cancel=cancel)
        recorded = trial.transition
        if (not step.committed or (step.observation.status, step.observation.state_id) !=
                (recorded.observation.status, recorded.observation.state_id)):
            raise ValueError("winning continuation changed during portfolio replay")
        transitions.append(step)
    expected = route[-1].finalization
    checked = driver.finalize(proof_fragment=expected.candidate if task.prover == "pvs" else None, cancel=cancel)
    _compare(expected.evidence, checked.evidence)
    if (expected.candidate, expected.match) != (checked.candidate, checked.match):
        raise ValueError("independent portfolio replay checked a different proof")
    manifest = RunManifest.for_native_proof_task(task, digest(portfolio.to_dict()), portfolio.policy_id,
                                                {"policy": portfolio.policy_id}, max_attempts=len(transitions))
    episode = NativeProofEpisode(task, manifest, initial, tuple(transitions), "ready", checked,
                                 route[-1].suggestion, tuple(progress))
    check_native_episode(episode)
    return episode
