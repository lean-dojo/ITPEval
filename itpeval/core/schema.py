"""Emit the checked-in JSON schemas with python -m itpeval.core.schema."""
import json

from itpeval.alignment import Correspondence, SourceRef
from itpeval.atp import (HammerEvidence, HOLSearchEvidence, LeanHornEvidence, LeanHornObservation, LeanHornProblem, RocqHornEvidence, RocqHornProblem,
                         SearchEvidence)
from itpeval.atp.agda import AgdaHornEvidence, AgdaHornObservation, AgdaHornProblem
from itpeval.atp.rocq import RocqHornObservation
from itpeval.atp.session import NativeATPSuggestion
from itpeval.atp.strategies import NativeStrategyEvidence, StrategyTrial
from itpeval.backends.external import DetachedCompletionManifest, DetachedTarget
from itpeval.backends.hol_tactics import HOLProofCheckpoint
from itpeval.backends.mizar.interaction import MizarArticleState
from itpeval.backends.projects import CompletionManifest
from itpeval.backends.pvs.interaction import PVSFinalization, PVSProofCheckpoint, PVSProofState
from itpeval.learning.native_proofs import ATPProgress, NativeProofEpisode
from itpeval.learning.portfolio import PortfolioTrial, ProofPortfolio
from itpeval.runtime.proof_driver import (NativeProofAction, NativeProofCheckpoint, NativeProofFinalization,
                                          NativeProofObservation, NativeProofTransition)
from itpeval.runtime.sessions import DocumentCheckpoint, StateHandle
from itpeval.runtime.interaction import AgdaAutoResult
from itpeval.verification.external import DetachedProofReceipt
from .capabilities import Capability
from .types import (Action, Artifact, ArtifactFile, Budgets, Context, DependencyEdge, EditableRegion,
                    EnvironmentSpec, Episode, FormalObject, Observation, TaskSpec, Transition,
                    VerificationEvidence)


def schemas():
    classes = (Action, AgdaAutoResult, AgdaHornEvidence, AgdaHornObservation, AgdaHornProblem, Artifact, ArtifactFile, ATPProgress, Budgets, Capability, CompletionManifest, Context, Correspondence, DependencyEdge,
               DetachedCompletionManifest, DetachedProofReceipt, DetachedTarget, DocumentCheckpoint, EditableRegion,
               EnvironmentSpec, Episode, FormalObject, HammerEvidence, HOLProofCheckpoint, HOLSearchEvidence, LeanHornEvidence,
               LeanHornObservation, LeanHornProblem, MizarArticleState, NativeATPSuggestion, NativeProofAction, NativeProofCheckpoint,
               NativeProofEpisode, NativeProofFinalization, NativeProofObservation, NativeProofTransition, NativeStrategyEvidence, Observation,
               PortfolioTrial, ProofPortfolio, PVSFinalization, PVSProofCheckpoint, PVSProofState, RocqHornEvidence, RocqHornObservation, RocqHornProblem,
               SearchEvidence, StateHandle, SourceRef, StrategyTrial, TaskSpec, Transition, VerificationEvidence)
    return {cls.__name__: cls.json_schema() for cls in classes}


if __name__ == "__main__":
    print(json.dumps(schemas(), indent=2, sort_keys=True))
