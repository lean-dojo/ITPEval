"""Bounded native checks with fair dispatch across provers and environments."""
from collections import Counter, OrderedDict, deque
from concurrent.futures import FIRST_COMPLETED, wait
from dataclasses import dataclass
from threading import Event

from itpeval.core.types import TaskSpec
from itpeval.verification.service import verify

from .pool import LocalPool, cancelled_evidence


@dataclass(frozen=True)
class Job:
    task: TaskSpec
    candidate: str | None
    prepared: object


def interleave_jobs(*sources):
    """Pull one job per iterable in turn until every source is exhausted."""
    active = deque(map(iter, sources))
    while active:
        source = active.popleft()
        try:
            job = next(source)
        except StopIteration:
            continue
        active.append(source)
        yield job


class _Pending:
    def __init__(self):
        self._provers = OrderedDict()
        self._size = 0

    def __len__(self):
        return self._size

    def append(self, index, job):
        prover = job.task.prover
        environment = job.task.environment_id
        if prover not in self._provers:
            self._provers[prover] = OrderedDict()
        by_environment = self._provers[prover]
        if environment not in by_environment:
            by_environment[environment] = deque()
        by_environment[environment].append((index, job))
        self._size += 1

    def pop(self, eligible=None):
        for prover in self._provers:
            if eligible is None or eligible(prover):
                break
        else:
            return None
        by_environment = self._provers[prover]
        environment, queue = by_environment.popitem(last=False)
        entry = queue.popleft()
        if queue:
            by_environment[environment] = queue
        if by_environment:
            self._provers.move_to_end(prover)
        else:
            del self._provers[prover]
        self._size -= 1
        return entry


def run_jobs(jobs, *, workers: int = 2, prover_limits=None, cancel: Event | None = None,
             writer=None, queue_limit: int | None = None):
    """Yield (input index, evidence) as they finish, invoking writer on the consuming thread."""
    if type(workers) is not int or workers <= 0:
        raise ValueError("workers must be a positive integer")
    limits = dict(prover_limits or {})
    if any(type(limit) is not int or limit <= 0 for limit in limits.values()):
        raise ValueError("prover limits must be positive integers")
    if queue_limit is None:
        queue_limit = workers * 4
    if type(queue_limit) is not int or queue_limit < workers:
        raise ValueError("queue_limit must be an integer at least the worker count")
    signal = cancel if cancel is not None else Event()
    if signal.is_set():
        return
    source = enumerate(jobs)
    pending = _Pending()
    exhausted = False
    busy = Counter()
    active = {}

    def eligible(prover):
        return busy[prover] < limits.get(prover, workers)

    with LocalPool(workers, cancel=signal, checker=verify) as pool:
        try:
            while True:
                while not exhausted and not signal.is_set() and len(active) + len(pending) < queue_limit:
                    try:
                        index, job = next(source)
                    except StopIteration:
                        exhausted = True
                        break
                    pending.append(index, job)
                while not signal.is_set() and len(active) < workers:
                    item = pending.pop(eligible)
                    if item is None:
                        break
                    index, job = item
                    prover = job.task.prover
                    future = pool.submit(job)
                    active[future] = index, prover
                    busy[prover] += 1
                ready = []
                if active:
                    completed, _ = wait(active, return_when=FIRST_COMPLETED)
                    for future in completed:
                        index, prover = active.pop(future)
                        busy[prover] -= 1
                        if not busy[prover]:
                            del busy[prover]
                        ready.append((index, future.result()))
                elif signal.is_set() and pending:
                    index, job = pending.pop()
                    ready.append((index, cancelled_evidence(job.task)))
                else:
                    break
                for index, evidence in ready:
                    if writer is not None:
                        writer(index, evidence)
                    yield index, evidence
        finally:
            if active:
                signal.set()
