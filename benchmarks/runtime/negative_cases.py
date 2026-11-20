"""Exercise malformed reviewed submissions and missing completions with each native backend."""
import argparse
import json
import shutil
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, prover_ids
from itpeval.environments import prepare_project
from itpeval.verification.service import verify

MALFORMED = {"acl2": ":hints :malformed-hints", "agda": "= (", "hol-light": "ALL_TAC THEN",
             "hol4": "ALL_TAC THEN", "isabelle": "by (", "lean4": "exact (",
             "metamath": "undeclared-label", "mizar": "thus ;", "pvs": "(grind",
             "rocq": "exact (."}


OPEN_PROOFS = {"lean4": "skip", "rocq": "idtac.", "pvs": "(skip)"}


def qualify(prover, prefix, cache, output):
    with TemporaryDirectory() as tmp:
        project = Path(tmp) / "project"
        shutil.copytree(curated_project(prover), project)
        path = project / "completion.json"
        manifest = json.loads(path.read_bytes())
        candidate = MALFORMED[prover]
        manifest["allowed_edits"].append(candidate)
        unfinished = OPEN_PROOFS.get(prover)
        if unfinished and unfinished not in manifest["allowed_edits"]:
            manifest["allowed_edits"].append(unfinished)
        path.write_text(json.dumps(manifest, sort_keys=True) + "\n")
        env = prepare_project(prover, project, prefix=prefix, cache=cache,
                              project_name="itpeval/malformed/" + prover)
        task = build_task(env)
        missing = verify(task, None, prepared=env)
        open_proof = verify(task, unfinished, prepared=env) if unfinished else None
        malformed = verify(task, candidate, prepared=env)
    output.mkdir(parents=True, exist_ok=True)
    record = {"prover": prover, "environment_id": env.environment_id, "prover_build": env.spec.prover_build,
              "candidate": candidate, "task": task.to_dict(), "missing": missing.to_dict(),
              "malformed": malformed.to_dict()}
    if open_proof is not None:
        record["unfinished_candidate"] = unfinished
        record["native_unfinished"] = open_proof.to_dict()
    (output / (prover + ".json")).write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    return (missing.task_success is False and missing.checker_outcome == "incomplete"
            and malformed.task_success is False and malformed.execution_outcome == "exited"
            and malformed.checker_outcome == "rejected"
            and (prover != "pvs" or "Error in script for formula" in malformed.stdout + malformed.stderr)
            and (open_proof is None or (open_proof.checker_outcome == "incomplete"
                                        and open_proof.execution_outcome == "exited")))


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--prefix", type=Path, required=True)
    cli.add_argument("--cache", type=Path, required=True)
    cli.add_argument("--output", type=Path, required=True)
    cli.add_argument("--prover", action="append", choices=prover_ids())
    cli.add_argument("--workers", type=int, default=1)
    args = cli.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as workers:
        results = list(workers.map(lambda p: qualify(p, args.prefix, args.cache, args.output),
                                   args.prover or prover_ids()))
    raise SystemExit(0 if all(results) else 1)
