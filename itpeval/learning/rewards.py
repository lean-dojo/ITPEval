"""Map task evidence to trainer signals while accounting for every check."""

from dataclasses import dataclass

from itpeval.core.types import TaskSpec, VerificationEvidence


@dataclass(frozen=True)
class Reward:
    value: float | None
    disposition: str


def proof_reward(task: TaskSpec, evidence: VerificationEvidence) -> Reward:
    """Score a completed proof or definitive rejection. Unscorable attempts have value None."""
    if evidence.task_id != task.task_id or evidence.environment_id != task.environment_id:
        raise ValueError("evidence belongs to another task or environment")
    if task.operation != "proof_completion":
        return Reward(None, "outside_proof_task")
    if evidence.task_success is None:
        return Reward(None, "infrastructure_failure")
    if evidence.task_success:
        complete = (evidence.execution_outcome == "exited" and evidence.checker_outcome == "accepted"
                    and evidence.target_preservation == "preserved" and evidence.completion_status == "proved"
                    and dict(evidence.obligations) == {name: "discharged" for name in task.obligations}
                    and bool(evidence.evidence_references))
        if not complete:
            raise ValueError("successful proof evidence is missing target, obligation or checker confirmation")
    elif (evidence.execution_outcome, evidence.checker_outcome) not in {
        ("exited", "rejected"), ("exited", "incomplete"), ("exited", "policy_rejected"),
        ("not_run", "incomplete"), ("not_run", "policy_rejected"),
    }:
        raise ValueError("zero proof reward requires a definitive checker or edit policy rejection")
    return Reward(1.0 if evidence.task_success else 0.0, "scored")
