"""Exercise portable checkpoints and independent document forks on native provers."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.registry import curated_project, get_backend, prover_ids
from itpeval.cli.lib import default_prefix
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.runtime.sessions import DocumentCheckpoint, DocumentSession


def exercise(prover, prefix, cache):
    backend = get_backend(prover)
    prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    task = backend.build_task(prepared)
    session = backend.open_document(task, prepared=prepared)
    source = (prepared.project / task.artifact.entrypoint).read_bytes()
    handle, accepted = session.submit_document(session.handle, source)
    checkpoint = session.checkpoint(handle)
    branch = session.fork(handle)
    _, rejected = branch.submit(branch.handle, task.allowed_edits[1])
    portable = DocumentCheckpoint.from_dict(json.loads(json.dumps(checkpoint.to_dict())))
    restored, replayed = DocumentSession.from_checkpoint(task, prepared, portable)
    if not (accepted.task_success is True and rejected.task_success is False and replayed.task_success is True
            and session.checkpoint(handle) == restored.checkpoint(restored.handle) == checkpoint
            and len({handle.session_id, branch.handle.session_id, restored.handle.session_id}) == 3
            and replayed.artifact_id == accepted.artifact_id):
        raise RuntimeError(f"{prover}: checkpoint, fork or replay disagreed with the original task")
    return {"prover": prover, "task_id": task.task_id, "environment_id": prepared.environment_id,
            "prover_build": prepared.spec.prover_build, "original": accepted.checker_outcome,
            "fork": rejected.checker_outcome, "restored": replayed.checker_outcome,
            "artifact_id": accepted.artifact_id}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, default=default_prefix())
    parser.add_argument("--provers", nargs="+", choices=prover_ids(), default=prover_ids())
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    def run(prover):
        row = exercise(prover, args.prefix, cache)
        print(prover, row["original"], row["fork"], row["restored"], flush=True)
        return row

    with TemporaryDirectory(prefix="itpeval-sessions-") as directory:
        cache = Path(directory)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            order = sorted(set(args.provers), key=lambda prover: (prover != "hol-light", prover))
            rows = list(pool.map(run, order))
        jsonl(args.output, sorted(rows, key=lambda row: row["prover"]))


if __name__ == "__main__":
    main()
