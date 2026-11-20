"""Standalone TPTP search and native proof replay in Isabelle, Lean, and Rocq."""

from .hol import HOLSearchEvidence
from .isabelle import HammerEvidence, PremisePool, SuggestedProof, run_sledgehammer
from .lean import (
    LeanHornEvidence, LeanHornHypothesis, LeanHornObservation, LeanHornProblem, observe_lean_horn, run_horn_search,
)
from .rocq import (
    RocqHornEvidence, RocqHornHypothesis, RocqHornObservation, RocqHornProblem,
    observe_rocq_horn, run_rocq_horn_search,
)
from .search import SOLVERS, PreparedSolver, SearchEvidence, SolverBuild, prepare_solver, solve_tptp
from .session import NativeATPSuggestion

__all__ = [
    "SOLVERS",
    "HammerEvidence",
    "HOLSearchEvidence",
    "LeanHornEvidence",
    "LeanHornHypothesis",
    "LeanHornObservation",
    "LeanHornProblem",
    "NativeATPSuggestion",
    "PremisePool",
    "PreparedSolver",
    "RocqHornEvidence",
    "RocqHornHypothesis",
    "RocqHornObservation",
    "RocqHornProblem",
    "SearchEvidence",
    "SolverBuild",
    "SuggestedProof",
    "observe_lean_horn",
    "observe_rocq_horn",
    "prepare_solver",
    "run_horn_search",
    "run_rocq_horn_search",
    "run_sledgehammer",
    "solve_tptp",
]
