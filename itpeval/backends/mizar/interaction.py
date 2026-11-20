"""Reviewed Mizar article revisions with native thesis and diagnostic feedback."""

from dataclasses import dataclass
from typing import Literal

from itpeval.core.records import Record
from itpeval.core.types import Artifact
from itpeval.runtime.sessions import DocumentSession
from itpeval.verification.policies import candidate_from_bytes
from itpeval.verification.service import _document_slot, verify_document

from .diagnostics import MizarProofTrace, _article_revision, _reviewed_template, _trace_article, _TraceError


@dataclass(frozen=True)
class MizarArticleState(Record):
    status: Literal["open", "closed", "rejected", "cancelled", "unavailable"]
    trace: MizarProofTrace | None = None
    message: str = ""

    @property
    def theses(self):
        return self.trace.theses if self.trace is not None else ()

    @property
    def diagnostics(self):
        return self.trace.diagnostics if self.trace is not None else ()


class MizarArticleSession(DocumentSession):
    """One native observation per revision, with fresh strict checking on finalization."""

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        self._template = _reviewed_template(task, prepared)
        self._candidate = None
        self._state = None

    @property
    def candidate(self) -> str | None:
        """Return the current proof fragment when its fixed source bytes were preserved."""
        with self._lock:
            return self._candidate

    def inspect(self, handle, *, cancel=None) -> MizarArticleState:
        """Read the stored native observation or inspect the initial open article."""
        with self._lock:
            self._require(handle)
            if self._state is None or self._state.status == "cancelled" and not (cancel and cancel.is_set()):
                self._state = self._trace_candidate(self._candidate, cancel)
            return self._state

    def step(self, handle, candidate, *, cancel=None):
        """Replace the reviewed proof slot and retain the revision even when it fails."""
        return self.submit(handle, candidate, cancel=cancel)

    def _fork_session(self):
        child = MizarArticleSession(self.task, self.prepared)
        child._candidate, child._state = self._candidate, self._state
        return child

    def reset(self):
        with self._lock:
            handle = super().reset()
            self._candidate = self._state = None
            return handle

    def _document_candidate(self, document):
        if not isinstance(document, Artifact):
            if not isinstance(document, (str, bytes)):
                raise TypeError("document must be an Artifact, str or bytes")
            files = {file.path: file.data for file in self.task.artifact.files}
            files[self.task.artifact.entrypoint] = document.encode("utf-8") if isinstance(document, str) else document
            document = Artifact.from_files(self.task.artifact.entrypoint, files)
        slot = _document_slot(self.task, document, self._template)
        return candidate_from_bytes(self.task, slot)

    def _observe_submission(self, verifier, submission, *, cancel=None):
        if verifier is not verify_document and submission is not None and not isinstance(submission, str):
            raise TypeError("a Mizar proof fragment must be text")
        try:
            self._candidate = self._document_candidate(submission) if verifier is verify_document else submission
        except ValueError as exc:
            self._candidate = None
            self._state = MizarArticleState("rejected", message=str(exc))
        else:
            self._state = self._trace_candidate(self._candidate, cancel)
        return self._state

    def _trace_candidate(self, candidate, cancel):
        if cancel is not None and cancel.is_set():
            return MizarArticleState("cancelled", message="Mizar observation cancelled")
        try:
            artifact = _article_revision(self.task, candidate)
        except ValueError as exc:
            return MizarArticleState("rejected", message=str(exc))
        try:
            trace = _trace_article(self.task, artifact, self.prepared, cancel=cancel)
        except _TraceError as exc:
            return MizarArticleState("cancelled" if exc.outcome == "cancelled" else "unavailable", message=str(exc))
        except (OSError, ValueError, RuntimeError) as exc:
            return MizarArticleState("unavailable", message=str(exc))

        # Native acceptance of the structurally valid article can coexist with
        # a blank reviewed slot. Only a submitted proof can close that task.
        if candidate is None or not candidate.strip():
            return MizarArticleState("open", trace)
        if trace.article_checked:
            return MizarArticleState("closed", trace)
        if trace.diagnostics:
            return MizarArticleState("rejected", trace)
        return MizarArticleState("unavailable", trace, "Mizar did not establish the target")
