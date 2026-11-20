"""Bounded worker pool for supervised verification jobs."""
from concurrent.futures import ThreadPoolExecutor
from threading import Event

from itpeval.core.types import VerificationEvidence
from itpeval.verification.service import verify


def cancelled_evidence(task):
    return VerificationEvidence(task.task_id, task.environment_id, task.artifact.artifact_id,
                                "cancelled", "not_run", None, "unchecked", "unknown")


class LocalPool:
    """Own worker threads and the cancellation signal for one or more batches.

    Each submission starts a fresh native attempt. A failed Python worker
    produces structured infrastructure evidence and the thread can take new work.
    The scheduler adds queue backpressure and per-prover limits to this pool.
    """

    def __init__(self, workers: int, *, cancel=None, checker=verify):
        self._workers = ThreadPoolExecutor(max_workers=workers)
        self.cancel = cancel if cancel is not None else Event()
        self._checker = checker

    def submit(self, job):
        return self._workers.submit(self._verify, job)

    def _verify(self, job):
        task = job.task
        if self.cancel.is_set():
            return cancelled_evidence(task)
        try:
            return self._checker(task, job.candidate, prepared=job.prepared, cancel=self.cancel)
        except Exception as exc:
            return VerificationEvidence(task.task_id, task.environment_id, task.artifact.artifact_id,
                                        "backend_error", "not_run", None, "unchecked", "unknown",
                                        stderr=f"{type(exc).__name__}: {exc}")

    def close(self, *, cancel=False):
        if cancel:
            self.cancel.set()
        self._workers.shutdown(wait=True)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close(cancel=exc_type is not None)
