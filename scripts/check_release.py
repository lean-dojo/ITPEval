"""Check the native receipts and cross-route identities of a Linux release."""
import argparse
import base64
import hashlib
import json
import re
from pathlib import Path

from itpeval.backends.registry import get_backend, prover_ids
from itpeval.core.episodes import Episode
from itpeval.core.records import digest
from itpeval.core.types import Artifact, TaskSpec, VerificationEvidence
from itpeval.learning.episodes import check_episode
from itpeval.learning.rewards import proof_reward
from itpeval.runtime.sessions import StateHandle


OPERATIONS = {"installed_package", "check_artifact", "proof_completion", "edit_document", "reset",
              "inspect_declarations", "end_to_end", "episode_replay", "evaluation_parity", "fixed_context"}
FIELDS = ("task_id", "environment_id", "artifact_id", "execution_outcome", "checker_outcome", "task_success",
          "target_preservation", "completion_status", "obligations", "evidence_references")
ROUTES = {"sdk", "sync", "batch", "posthoc", "trainer"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def evidence_file(root, relative):
    path = (root / relative).resolve(strict=True)
    require(path.is_relative_to(root.resolve()) and path.is_file(), f"evidence outside {root}: {relative}")
    return path


def read(path):
    return json.loads(path.read_bytes())


def native(row, env, success):
    """Decode the full record before comparing portable evidence across fresh processes."""
    result = VerificationEvidence.from_dict(row)
    require(result.environment_id == env and result.execution_outcome == "exited"
            and result.task_success is success and result.returncode is not None
            and (result.returncode == 0 if success else True), "missing native checker outcome")
    if success and result.completion_status == "proved":
        require(result.target_preservation == "preserved" and result.obligations
                and all(status == "discharged" for _, status in result.obligations), "missing target obligations")
    return {k: row[k] for k in FIELDS}


def required_operations(prover):
    # A release covers every operation labelled available by this version of the
    # registry, including optional instrumentation in its own pinned environment.
    available = {c.operation for c in get_backend(prover).capabilities()
                 if c.status in {"experimental", "implemented/tested"}}
    return OPERATIONS | available | ({"bounded_equivalence"} if prover == "lean4" else set())


def check_episode_receipts(directory, detail, env):
    dataset = read(evidence_file(directory, detail["dataset"]))
    path = evidence_file(directory, detail["episode"])
    episode = Episode.from_dict(read(path))
    task = TaskSpec.from_dict(dataset["task"])
    final = check_episode(episode, task)
    attempt = read(path.with_name("attempts.jsonl"))
    supervised = read(path.with_name("supervised.jsonl"))
    raw = base64.b64decode(dataset["source_base64"], validate=True)
    require(episode.manifest["dataset_id"] == digest(dataset)
            and dataset["target"]["source_hash"] == hashlib.sha256(raw).hexdigest()
            and task.environment_id == env
            and dataset["target"]["declaration_id"] == detail["declaration_id"]
            and dataset["target"]["context_id"] == detail["context_id"] == dataset["context"]["context_id"]
            and all(dataset[k]["environment_id"] == env for k in ("context", "target")), "dataset identity mismatch")
    require(attempt["episode"] == episode.to_dict() and attempt["reward"] == 1 and attempt["disposition"] == "scored"
            and supervised["task_id"] == task.task_id and supervised["completion"] == episode.final_candidate
            and [s.observation.task_success for s in episode.transitions] == [False, True]
            and proof_reward(task, final).value == 1, "episode and trainer export disagree")
    replay = read(evidence_file(directory, detail["replay"]))
    require((replay["run_id"], replay["task_id"], replay["environment_id"]) ==
            (episode.run_id, episode.task_id, env) and len(replay["transitions"]) == len(episode.transitions),
            "replay identities or number of transitions differ")
    for step, observed in zip(episode.transitions, replay["transitions"]):
        success = step.observation.task_success
        require(native(step.evidence, env, success) == native(observed, env, success), "native replay differs")
    require(native(replay["final"], env, True) == native(final.to_dict(), env, True), "final replay differs")
    return [native(episode.transitions[i].evidence, env, i == 1) for i in (1, 0)]


def check_parity(detail, env):
    cases = []
    for case, success in (("valid", True), ("invalid", False)):
        row = detail[case]
        require(row["agrees"] is True and set(row["native_evidence"]) == ROUTES, "missing evaluation route")
        for route in ROUTES:
            actual = native(row["native_evidence"][route], env, success)
            require(row["evidence"] == actual and row["evidence_hashes"][route] == digest(actual)
                    and row["rewards"][route] == int(success), f"{route} evidence or reward disagrees")
        cases.append(row["evidence"])
    return cases


def check_additional_runs(directory, prover, cases, wheel_hash):
    smoke = read(directory / "smoke.json")
    require(smoke["wheel_sha256"] == wheel_hash and smoke["prover"] == prover
            and smoke["task"] == "arith_2_plus_2" and smoke["version"] and smoke["returncode"] == 0
            and smoke["execution_outcome"] == "exited" and smoke["status"] == "ok"
            and re.fullmatch("[0-9a-f]{64}", smoke["log_sha256"]), "invalid installed CLI receipt")
    rejected = read(directory / "malformed" / (prover + ".json"))
    task = TaskSpec.from_dict(rejected["task"])
    missing = VerificationEvidence.from_dict(rejected["missing"])
    malformed = native(rejected["malformed"], task.environment_id, False)
    require(task.prover == prover and task.environment_id == rejected["environment_id"]
            and missing.task_id == task.task_id == malformed["task_id"]
            and missing.checker_outcome == "incomplete" and missing.task_success is False
            and malformed["checker_outcome"] == "rejected", "missing malformed or incomplete proof case")
    if prover in {"lean4", "rocq", "pvs"}:
        unfinished = native(rejected["native_unfinished"], task.environment_id, False)
        require(unfinished["checker_outcome"] == "incomplete" and unfinished["task_id"] == task.task_id,
                "open native proof goals were not recorded")
    if prover == "metamath":
        trainer = read(directory / "grpo/trainer.json")
        attempts = [json.loads(line) for line in (directory / "grpo/trainer-attempts.jsonl").read_text().splitlines()]
        require(trainer["steps"] == 1 and trainer["device"] == "cpu" and trainer["max_embedding_update"] > 0
                and trainer["rewards"] == [1.0, 0.0] and len(attempts) == 2, "missing trainer optimizer step")
        for index, attempt in enumerate(attempts):
            env = cases[index]["environment_id"]
            require(native(attempt["evidence"], env, index == 0) == cases[index]
                    and attempt["reward"] == trainer["rewards"][index], "training step used a different proof")
    if prover == "rocq":
        historical = read(directory / "published-translation.json")
        require(historical["population"] == "published" and set(historical["routes"]) == {"sync", "batch", "posthoc"},
                "missing a published translation route")
        for row in historical["routes"].values():
            require(row["verified"] is True and row["task_success"] is None
                    and row["raw_generated"] == historical["raw_generated"]
                    and row["evidence"]["completion_status"] == "statement_accepted"
                    and row["evidence"]["target_preservation"] == "unbound", "historical statement semantics changed")


def check_prover(prover, records):
    missing = required_operations(prover) - records.keys()
    require(not missing, f"missing operations {sorted(missing)}")
    env = records["end_to_end"][0]["environment_id"]
    require(all(records[k][0]["environment_id"] == env for k in OPERATIONS - {"inspect_declarations"}),
            "completion, replay and evaluation used different environments")
    record, path = records["end_to_end"]
    detail = read(path)
    cases = check_episode_receipts(path.parent, detail, env)
    require(cases == check_parity(read(records["evaluation_parity"][1]), env), "evaluation and replay disagree")
    for name in ("check_artifact", "proof_completion", "edit_document", "reset", "episode_replay"):
        require(records[name][1] == path, f"{name} disagrees on document receipt")
    require(native(detail["artifact"], env, True)["completion_status"] == "artifact_accepted", "missing artifact check")
    require(native(detail["valid_edit"], env, True) == cases[0] == native(detail["final"], env, True)
            and native(detail["incorrect_edit"], env, False) == cases[1], "document edits and replay disagree")
    require(detail["alternate"] and all(native(row, env, True)["completion_status"] == "proved"
                                        for row in detail["alternate"]), "missing alternative proof")
    reset = detail["reset"]
    old, new = (StateHandle.from_dict(reset[key]) for key in ("old_handle", "new_handle"))
    require(reset["stale_rejected"] is True and old.environment_id == new.environment_id == env
            and old.session_id == new.session_id and new.worker_generation > old.worker_generation
            and new.revision == 0, "reset did not reject an obsolete handle")
    edits = read(records["fixed_context"][1])
    require(set(edits) == {"changed_target", "deleted_declaration", "admission", "added_assumption"},
            "missing fixed-context cases")
    for case, row in edits.items():
        e = VerificationEvidence.from_dict(row["evidence"])
        require(e.task_id == cases[0]["task_id"] and e.environment_id == env and e.task_success is False
                and e.checker_outcome == "policy_rejected" and e.execution_outcome == "not_run", "edit policy mismatch")
        submitted = Artifact.from_dict(row["submitted_artifact"])
        require(e.artifact_id == submitted.artifact_id
                and e.target_preservation == ("preserved" if case == "admission" else "violated")
                and "submitted_artifact:" + submitted.artifact_id in e.evidence_references,
                "rejection does not identify the submitted document and target")
    document = read(path.parent / "document-check.json")
    accepted = native(document["accepted"], env, True)
    submitted = Artifact.from_dict(document["submitted_artifact"])
    handle = StateHandle.from_dict(document["last_revision"])
    require(accepted["task_id"] == cases[0]["task_id"] and accepted["completion_status"] == "proved"
            and "submitted_artifact:" + submitted.artifact_id in accepted["evidence_references"]
            and handle.environment_id == env and handle.revision == 2
            and document["finalized_deleted_declaration"] == edits["deleted_declaration"]["evidence"],
            "document finalization lost the submitted revision")
    row, extraction_path = records["inspect_declarations"]
    x = read(extraction_path)
    require(x["prover"] == prover and x["environment_id"] == row["environment_id"] and not x["failed"]
            and x["fresh_runs"] >= 2 and x["cache_replay"] is True and x["known_answers"]
            and all(value is True for value in x["known_answers"].values()) and x["succeeded"]
            and x["dataset_rows"] == x["declarations"] >= 2
            and all(re.fullmatch("[0-9a-f]{64}", x["normalized_sha256"][name])
                    for name in ("report.json", "declarations.jsonl", "contexts.jsonl", "dependencies.jsonl")),
            "extraction receipt lacks independent native runs or known answers")
    builds = read(records["installed_package"][1])
    for kind in ("wheel", "sdist"):
        require(builds[kind]["prover_build"] == record["prover_build"]
                and native(builds[kind]["evidence"], env, True) == cases[0], f"{kind} used another build or result")
    check_additional_runs(path.parent, prover, cases, builds["wheel"]["wheel_sha256"])
    for op in records.keys() - OPERATIONS:
        row, receipt = records[op]
        checked = read(receipt)
        if op == "bounded_equivalence":
            positive, negative = (checked["results"][name] for name in ("Counts.next_index_zero", "Counts.nextIndex"))
            require(positive["environment_id"] == negative["environment_id"] == row["environment_id"]
                    and positive["status"] == "equivalence established" and positive["forward"] and positive["backward"]
                    and negative["status"] == "equivalence not established", "missing bounded-equivalence results")
        else:
            require(checked["prover"] == prover and checked["environment_id"] == row["environment_id"]
                    and checked["prover_build"] == row["prover_build"] and checked["operations"].get(op) is True
                    and checked["native"], f"missing native evidence for {op}")
    return builds["wheel"]["wheel_sha256"], builds["sdist"]["sdist_sha256"]


def check(reports, provers=None, distributions=None):
    selected = set(provers or prover_ids())
    seen = {p: {} for p in selected}
    for path in reports:
        for line in path.read_text().splitlines():
            row = json.loads(line)
            prover, op = row["prover"], row["operation"]
            require(prover in selected and op not in seen[prover] and row["status"] == "implemented/tested"
                    and row["prover_build"] and re.fullmatch("[0-9a-f]{64}", row["environment_id"]),
                    f"{prover}/{op}: unexpected, duplicate or unqualified record")
            seen[prover][op] = (row, evidence_file(path.parent, row["evidence_path"]))
    hashes = set()
    for prover, records in seen.items():
        try:
            hashes.add(check_prover(prover, records))
        except (IndexError, KeyError, TypeError, ValueError, OSError) as error:
            raise ValueError(f"{prover}: {error}") from error
    require(len(hashes) == 1 and all(re.fullmatch("[0-9a-f]{64}", h) for h in next(iter(hashes))),
            "provers qualified different release archives")
    if distributions:
        wheel, = distributions.glob("*.whl")
        sdist, = distributions.glob("*.tar.gz")
        require(next(iter(hashes)) == tuple(hashlib.sha256(p.read_bytes()).hexdigest() for p in (wheel, sdist)),
                "supplied distributions differ from tested archives")
    print(f"Verified {len(seen)} prover reports and {sum(map(len, seen.values()))} operations.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", nargs="+", type=Path)
    parser.add_argument("--prover", action="append", choices=prover_ids(), help="check a single CI matrix shard")
    parser.add_argument("--distributions", type=Path, help="verify the exact wheel and source archive")
    args = parser.parse_args()
    check(args.reports, args.prover, args.distributions)
