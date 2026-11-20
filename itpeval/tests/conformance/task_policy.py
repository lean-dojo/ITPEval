"""Exercise fixed targets and assumptions using the selected prover's document syntax."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path

from itpeval.backends.projects import CompletionManifest, build_task
from itpeval.backends.registry import curated_project, prover_ids
from itpeval.core.types import Artifact
from itpeval.environments import prepare_project
from itpeval.learning.qualification import _record
from itpeval.runtime.sessions import DocumentSession
from itpeval.verification.service import verify_document

# These fragments are inputs to the policy gate. A candidate never receives authority
# to insert them into the trusted declaration or add surrounding declarations.
FRAGMENTS = {
    "lean4": ("sorry", "axiom extra : False"),
    "rocq": ("Admitted.", "Axiom extra : False."),
    "isabelle": ("sorry", 'axiomatization where extra: False'),
    "hol-light": ('new_axiom `F`', 'let extra = new_axiom `F`;;'),
    "acl2": ("(skip-proofs (defthm extra nil))", "(defaxiom extra nil)"),
    "agda": ("{!!}", "postulate extra : ⊥"),
    "hol4": ("cheat", 'val extra = new_axiom ("extra", ``F``);'),
    "metamath": ("?", "extra $a |- pair x y $."),
    "mizar": ("::$P-\nproof end;\n::$P+", "assume contradiction;"),
    "pvs": ("(postpone)", "extra: AXIOM FALSE"),
}


def qualify(prover, prefix, cache, output, report):
    prepared = prepare_project(prover, curated_project(prover), prefix=prefix, cache=cache)
    task = build_task(prepared)
    m = CompletionManifest.from_dict(json.loads((prepared.project / task.manifest_path).read_bytes()))
    files = {name: (prepared.project / name).read_bytes() for name in m.files}
    source = files[m.entrypoint].decode("utf-8")
    if source.count(m.anchor) != 1 or m.target not in m.anchor:
        raise ValueError("proof policy fixture lacks a unique target anchor")
    admission, assumption = FRAGMENTS[prover]
    def document(entry):
        return Artifact.from_files(m.entrypoint, {**files, m.entrypoint: entry.encode("utf-8")})

    # Insert into the source before its native declaration. The admission instead
    # occupies only the proof slot, leaving the fixed declaration byte-identical.
    edits = {
        "changed_target": document(source.replace(m.target, "other_target")),
        "deleted_declaration": document(source.replace(m.anchor, "")),
        "admission": document(source.replace(m.anchor, m.anchor.replace(m.proof_slot, admission))),
        "added_assumption": document(source.replace(m.anchor, assumption + "\n" + m.anchor)),
    }
    session = DocumentSession(task, prepared)
    valid = document(source)
    handle, positive = session.submit_document(session.handle, valid)
    data = {}
    for key, submitted in edits.items():
        if key == "deleted_declaration":
            handle, result = session.submit_document(handle, submitted)
        else:
            result = verify_document(task, submitted, prepared=prepared)
        data[key] = {"submitted_artifact": submitted.to_dict(), "evidence": result.to_dict()}
    final = session.finalize(handle)
    path = output / prover / "edit-policy.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    replay = {"submitted_artifact": valid.to_dict(), "accepted": positive.to_dict(),
              "last_revision": handle.to_dict(), "finalized_deleted_declaration": final.to_dict()}
    (path.parent / "document-check.json").write_text(json.dumps(replay, ensure_ascii=False, indent=2) + "\n")
    passed = (positive.task_success is True and positive.execution_outcome == "exited"
              and "submitted_artifact:" + valid.artifact_id in positive.evidence_references
              and final.to_dict() == data["deleted_declaration"]["evidence"])
    for key, submitted in edits.items():
        ev = data[key]["evidence"]
        passed &= (ev["task_success"] is False and ev["checker_outcome"] == "policy_rejected"
                   and ev["execution_outcome"] == "not_run" and ev["artifact_id"] == submitted.artifact_id
                   and "submitted_artifact:" + submitted.artifact_id in ev["evidence_references"]
                   and ev["target_preservation"] == ("preserved" if key == "admission" else "violated"))
    _record(report, [{"prover": prover, "environment_id": prepared.environment_id,
                      "prover_build": prepared.spec.prover_build, "operation": "fixed_context",
                      "status": "implemented/tested" if passed else "failed",
                      "evidence_path": os.path.relpath(path, report.parent)}])
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prover", action="append", choices=prover_ids())
    for key in ("prefix", "cache", "output", "report"):
        parser.add_argument("--" + key, required=True, type=Path)
    args = parser.parse_args()
    passed = [qualify(p, args.prefix, args.cache, args.output, args.report) for p in args.prover or prover_ids()]
    raise SystemExit(0 if all(passed) else 1)


if __name__ == "__main__":
    main()
