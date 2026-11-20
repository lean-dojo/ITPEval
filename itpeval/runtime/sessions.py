"""Document revision sessions. Each check starts its own native process."""
from base64 import b64decode, b64encode
from dataclasses import dataclass
from threading import RLock
from typing import Literal
from uuid import uuid4

from itpeval.core.records import Record
from itpeval.core.types import Artifact
from itpeval.verification.service import verify, verify_document


@dataclass(frozen=True)
class StateHandle(Record):
    environment_id: str
    session_id: str
    state_kind: str
    worker_generation: int
    revision: int


@dataclass(frozen=True)
class DocumentCheckpoint(Record):
    """The last source submission, portable between sessions with the same lock."""

    task_id: str
    environment_id: str
    input_kind: Literal["initial", "fragment", "document", "artifact"]
    payload: str | Artifact | None

    def __post_init__(self):
        expected = {"initial": type(None), "fragment": (str, type(None)),
                    "document": str, "artifact": Artifact}
        if self.input_kind not in expected or not isinstance(self.payload, expected[self.input_kind]):
            raise ValueError("checkpoint payload does not match its input kind")


class DocumentSession:
    def __init__(self, task, prepared):
        if task.environment_id != prepared.environment_id:
            raise ValueError("session environment does not match the task")
        self.task, self.prepared = task, prepared
        self._id, self._generation, self._revision = uuid4().hex, 0, 0
        self._submission = None
        self._verifier = verify
        self._lock = RLock()

    @property
    def handle(self):
        return StateHandle(self.task.environment_id, self._id, "document", self._generation,
                           self._revision)

    def fork(self, handle):
        """Copy the current revision into an independent in-memory document session."""
        with self._lock:
            self._require(handle)
            child = self._fork_session()
            child._submission = self._submission
            child._verifier = self._verifier
            child._revision = self._revision
            return child

    def _fork_session(self):
        return DocumentSession(self.task, self.prepared)

    def checkpoint(self, handle) -> DocumentCheckpoint:
        """Store the last submitted input without carrying live prover state."""
        with self._lock:
            self._require(handle)
            submission = self._submission
            if self._revision == 0:
                kind, payload = "initial", None
            elif self._verifier is verify:
                kind, payload = "fragment", submission
            elif isinstance(submission, Artifact):
                kind, payload = "artifact", submission
            else:
                source = submission.encode("utf-8") if isinstance(submission, str) else submission
                kind, payload = "document", b64encode(source).decode("ascii")
            return DocumentCheckpoint(self.task.task_id, self.task.environment_id, kind, payload)

    @classmethod
    def from_checkpoint(cls, task, prepared, checkpoint: DocumentCheckpoint, **options):
        """Open a new session and check the saved submission with the native prover."""
        if (checkpoint.task_id, checkpoint.environment_id) != (task.task_id, prepared.environment_id):
            raise ValueError("checkpoint belongs to another task or environment")
        session = cls(task, prepared)
        if checkpoint.input_kind == "initial":
            prepared.validate()
            return session, None
        if checkpoint.input_kind == "fragment":
            _, evidence = session.submit(session.handle, checkpoint.payload, **options)
        else:
            document = checkpoint.payload
            if checkpoint.input_kind == "document":
                document = b64decode(document, validate=True)
            _, evidence = session.submit_document(session.handle, document, **options)
        return session, evidence

    def _require(self, handle):
        if handle != self.handle:
            raise ValueError("stale or foreign document handle")

    def submit(self, handle, candidate, **options):
        return self._submit(handle, candidate, verify, options)

    def submit_document(self, handle, document, **options):
        """Record a full document revision, including one rejected by the edit policy."""
        return self._submit(handle, document, verify_document, options)

    def _submit(self, handle, submission, verifier, options):
        with self._lock:
            self._require(handle)
            evidence = self._observe_submission(verifier, submission, **options)
            self._submission = submission
            self._verifier = verifier
            self._revision += 1
            return self.handle, evidence

    def _observe_submission(self, verifier, submission, **options):
        return verifier(self.task, submission, prepared=self.prepared, **options)

    def reset(self):
        with self._lock:
            self._submission = None
            self._verifier = verify
            self._revision = 0
            self._generation += 1
            return self.handle

    def replay(self, candidates, **options):
        return self._replay(candidates, self.submit, options)

    def replay_documents(self, documents, **options):
        """Reset and submit a sequence of full revisions, including rejected edits."""
        return self._replay(documents, self.submit_document, options)

    def _replay(self, submissions, submit, options):
        with self._lock:
            handle = self.reset()
            observations = []
            for submission in submissions:
                handle, observation = submit(handle, submission, **options)
                observations.append(observation)
            return handle, observations

    def finalize(self, handle, **options):
        with self._lock:
            self._require(handle)
            return self._verifier(self.task, self._submission, prepared=self.prepared, **options)
