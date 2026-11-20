"""Work on an open assertion in the native Metamath Proof Assistant."""
from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import islice
from pathlib import Path
import re
from tempfile import TemporaryDirectory

from itpeval.core.records import Record
from itpeval.runtime.interaction import _ProofSession
from itpeval.verification.policies import validate_inputs


_LABEL = re.compile(r"[A-Za-z0-9_.-]+")
_ACTION_LIMIT = 256
_PROOF_STEP = re.compile(r"^\s*(\d+)\s+(\S+)=(\S+)\s+(\$[?faep])\s*(.*)$")
_ASSISTANT_PROMPT = "MM-PA> "
_PROOF_START = "---------Clip out the proof below this line to put it in the source file:\n"


@dataclass(frozen=True)
class ProofStep(Record):
    index: int
    target_label: str
    applied_label: str
    kind: str
    expression: str


@dataclass(frozen=True)
class ProofState(Record):
    task_id: str
    environment_id: str
    source_path: str
    target: str
    steps: tuple[ProofStep, ...]
    candidate: str | None
    diagnostic: str = ""

    @property
    def open_steps(self):
        return tuple(step for step in self.steps if step.applied_label == "?")


def _steps(output: str) -> tuple[ProofStep, ...]:
    rows = []
    for line in output.rstrip().splitlines():
        match = _PROOF_STEP.fullmatch(line)
        if match:
            index, target, label, kind, expression = match.groups()
            rows.append(ProofStep(int(index), target, label, kind, expression))
        elif rows and line.startswith(" "):
            # The native display wraps long mathematical expressions.
            step = rows[-1]
            rows[-1] = replace(step, expression=step.expression + " " + line.strip())
        elif line.strip():
            raise ValueError("unexpected Metamath proof display: " + line[:160])
    if not rows:
        raise ValueError("Metamath returned no proof steps")
    return tuple(rows)


class MetamathProofSession(_ProofSession):
    """Assign reviewed labels to numbered native steps and verify the resulting proof.

    Each action replays the assignment history in a fresh native workspace.
    A complete proof-assistant display can still violate a distinct-variable
    constraint. Only `finalize` establishes native task success.
    """

    prover = "metamath"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        validate_inputs(task, task.artifact)
        if prepared.spec.checking_profile != "strict":
            raise ValueError("Metamath proof editing requires a strict project profile")
        if (not _LABEL.fullmatch(task.targets[0])
                or any(not _LABEL.fullmatch(part) for part in Path(task.artifact.entrypoint).parts)):
            raise ValueError("Metamath proof editing requires a plain entrypoint path and target label")
        self._history: list[tuple[int, str]] = []
        self._state = None

    def reset(self):
        self._history.clear()
        self._state = None
        return super().reset()

    def fork(self, handle):
        """Copy the committed assignment state without rerunning the assistant."""
        self.require(handle)
        branch = type(self)(self.task, self.prepared)
        branch._history = self._history.copy()
        branch._state, branch.candidate, branch.revision = self._state, self.candidate, self.revision
        return branch

    def _transaction(self, actions, cancel, *, prefix=False):
        entrypoint = self.task.artifact.entrypoint
        target = self.task.targets[0]
        commands = ["set scroll continuous", "set width 300", f'read "{entrypoint}"',
                    f"prove {target}", "show new_proof /all"]
        for index, label in actions:
            commands += [f"assign {index} {label}", "show new_proof /all"]
        commands += ["show new_proof /normal"]
        with TemporaryDirectory(prefix="itpeval-mm-proof-") as tmp:
            root = Path(tmp)
            self._editor_source("?").materialize(root)
            driver = root / ".itpeval-commands"
            if driver.exists():
                raise ValueError("reserved Metamath driver path is present in the project")
            driver.write_text("\n".join(commands) + "\n", encoding="ascii")
            raw = self._run([str(self.prepared.prefix / "metamath/bin/metamath")], root, cancel, driver)
        outputs = raw.split(_ASSISTANT_PROMPT)
        if len(outputs) != 4 + 2 * len(actions):
            raise RuntimeError("Metamath did not complete the assignment transaction: " + raw[-1600:])
        _, found, proof = outputs[-2].partition(_PROOF_START)
        proof, end, _ = proof.partition("$.")
        if not (found and end):
            raise ValueError("Metamath did not return a native proof fragment")
        labels = proof.split()
        if not labels or any(label != "?" and not _LABEL.fullmatch(label) for label in labels):
            raise ValueError("Metamath returned a malformed proof fragment")
        candidate = None if "?" in labels else " ".join(labels)

        def state(position, fragment=None):
            diagnostic = outputs[2 * position].strip() if position else ""
            return ProofState(self.task.task_id, self.environment_id, entrypoint, target,
                              _steps(outputs[1 + 2 * position]), fragment, diagnostic)

        final = state(len(actions), candidate)
        if not prefix:
            return final
        for position in range(1, len(actions) + 1):
            diagnostic = outputs[2 * position].strip()
            if diagnostic.startswith("?"):
                raise ValueError(f"Metamath assignment did not commit at replay step {position}: {diagnostic}")
        states = tuple(state(position) for position in range(len(actions)))
        # ASSIGN only fills unknown steps. Any state before the final
        # assignment therefore still has a hole and no complete candidate.
        if any(not observed.open_steps for observed in states):
            raise ValueError("saved Metamath prefix continued after a complete proof")
        return (*states, final)

    def inspect(self, handle, *, cancel=None):
        self.require(handle)
        if self._state is None:
            self._state = self._transaction(self._history, cancel)
        return self._state

    def _reviewed_assignment(self, index, label):
        return (type(index) is int and 0 < index <= 2**31 - 1 and isinstance(label, str)
                and _LABEL.fullmatch(label) is not None and label in self.task.proof_atoms)

    def assign(self, handle, index: int, label: str, *, cancel=None):
        self.require(handle)
        if not self._reviewed_assignment(index, label) or len(self._history) >= _ACTION_LIMIT:
            raise ValueError("expected a native step number and one of the task's reviewed labels")
        actions = [*self._history, (index, label)]
        state = self._transaction(actions, cancel)
        if state.diagnostic.startswith("?"):
            return self.handle, state
        self._history = actions
        self._state, self.candidate = state, state.candidate
        self.revision += 1
        return self.handle, state

    def replay_prefix(self, handle, assignments, *, cancel=None):
        """Restore initial and committed assignment states in one native run."""
        self.require(handle)
        if self._history:
            raise ValueError("Metamath replay_prefix requires an unused proof session")
        actions = list(islice(assignments, _ACTION_LIMIT + 1))
        if len(actions) > _ACTION_LIMIT or any(not isinstance(action, (tuple, list)) or len(action) != 2
                                               or not self._reviewed_assignment(*action) for action in actions):
            raise ValueError("expected a bounded prefix of reviewed Metamath assignments")
        actions = [tuple(action) for action in actions]
        states = self._transaction(actions, cancel, prefix=True)
        self._history = actions
        self._state, self.candidate = states[-1], states[-1].candidate
        self.revision = len(actions)
        return states
