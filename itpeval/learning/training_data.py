"""Export native extraction and proof episodes for local training."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from contextlib import ExitStack
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import build_task
from itpeval.core.episodes import Episode
from itpeval.corpus.contexts import ContextTable
from itpeval.core.types import TaskSpec, VerificationEvidence
from itpeval.corpus.datasets import premise_rows
from itpeval.corpus.parquet import write_rows_parquet
from itpeval.corpus.storage import digest, encode, read_jsonl
from itpeval.environments import load_project
from itpeval.learning.episodes import task_prompt
from itpeval.learning.native_proofs import NativeProofEpisode, check_native_episode
from itpeval.learning.rewards import proof_reward
from itpeval.learning.views import trajectory_rows


VIEWS = ("pretraining", "sft", "repair", "preference", "unpaired", "grpo", "trajectory", "retrieval", "proof_steps")
SHA256 = re.compile(r"[0-9a-f]{64}")


def _arrow_schemas(chat):
    import pyarrow as pa

    text = pa.string()
    integer = pa.int64()
    truth = pa.bool_()
    number = pa.float64()
    base = [("schema_version", pa.int32()), ("split", text)]
    identity = [(name, text) for name in ("task_id", "environment_id", "prover")]
    provenance = list(identity) + [("run_id", text)]
    message_list = pa.list_(pa.struct([("role", text), ("content", text)]))
    message = message_list if chat else text
    prompt = [("prompt", message)]
    completion = [("completion", message)]
    action = pa.struct([("schema_version", pa.int32()),
                       ("kind", text), ("raw_response", text), ("candidate", text)])
    feedback = [("execution_outcome", text), ("checker_outcome", text), ("task_success", truth),
                ("stdout", text), ("stderr", text), ("duration_ms", integer)]
    observation = pa.struct([("schema_version", pa.int32()), *feedback])
    native_action = pa.struct([("schema_version", pa.int32()), ("kind", text), ("text", text),
                               ("goal_path", pa.list_(integer)), ("step_index", integer)])
    native_state = pa.struct([("status", text), ("state_id", text), ("native_json", text)])
    evidence = pa.struct([
        ("schema_version", pa.int32()), ("task_id", text), ("environment_id", text), ("artifact_id", text),
        *feedback, ("target_preservation", text), ("completion_status", text),
        ("obligations", pa.list_(pa.list_(text))), ("returncode", integer),
        ("evidence_references", pa.list_(text)), ("workspace", text), ("peak_process_rss_bytes", integer),
        ("cpu_time_s", number), ("logs_truncated", truth),
    ])
    origins = pa.list_(pa.struct([(name, text) for name in
                                  ("prover", "environment_id", "source_path", "extraction_id")]))
    schemas = {
        "pretraining": [("text", text), ("source_sha256", text), ("origins", origins)],
        "sft": [*prompt, *completion, *provenance],
        "repair": [*prompt, *completion, *provenance, ("step", integer)],
        "preference": [*prompt, ("chosen", message), ("rejected", message), *identity,
                       ("chosen_run_id", text), ("rejected_run_id", text)],
        "unpaired": [*prompt, *completion, ("label", truth), *provenance],
        "grpo": [*prompt, *identity],
        "trajectory": [*provenance, ("step", integer), ("prompt", text), ("reward", number), ("disposition", text),
                       ("terminated", truth), ("truncated", truth),
                       ("action", action), ("observation", observation), ("evidence", evidence)],
        "retrieval": [(name, text) for name in
                      ("anchor", "positive", "prover", "environment_id", "context_id",
                       "declaration_id", "positive_id")],
        "proof_steps": [*provenance, ("step", integer), ("prompt", text), ("before", native_state),
                        ("action", native_action), ("feedback", native_state), ("committed", truth),
                        ("reward", number), ("terminated", truth), ("truncated", truth),
                        ("stop_reason", text), ("final_candidate", text), ("final_match", text),
                        ("final_evidence", evidence), ("atp_json", text), ("unapplied_atp_json", text)],
    }
    return {view: pa.schema(base + fields) for view, fields in schemas.items()}


def _sources(bundles, excluded):
    by_hash = defaultdict(list)
    locations = {}
    for bundle in bundles:
        report = json.loads((bundle / "report.json").read_bytes())
        for source_path in sorted(set(report["succeeded"])):
            key = report["sources"][source_path]
            if not SHA256.fullmatch(key):
                raise ValueError(f"invalid source hash in {bundle}")
            if key not in excluded:
                locations.setdefault(key, bundle / "blobs" / key[:2] / key[2:])
                by_hash[key].append({
                    "prover": report["prover"], "environment_id": report["environment_id"],
                    "source_path": source_path, "extraction_id": bundle.name,
                })
    for key, origins in sorted(by_hash.items()):
        raw = locations[key].read_bytes()
        if digest(raw) != key:
            raise ValueError(f"source blob does not match its receipt: {key}")
        yield {"text": raw.decode("utf-8"), "source_sha256": key, "origins": origins}


def _retrieval(bundles):
    seen = set()
    for bundle in bundles:
        declarations = {row["declaration_id"]: row for row in read_jsonl(bundle / "declarations.jsonl")}
        contexts = ContextTable(bundle)
        for row in premise_rows(bundle, visibility="reference", contexts=contexts):
            if row["proof_used_availability"] != "observed":
                continue
            query = row["declaration"]
            visible = contexts.visible_subset(query["context_id"], (edge["target_id"] for edge in row["proof_used"]))
            for edge in row["proof_used"]:
                premise = declarations.get(edge["target_id"])
                if premise is None or edge["target_id"] not in visible:
                    continue
                pair = (query["declaration_id"], premise["declaration_id"])
                if pair in seen or not query["statement"].strip() or not premise["statement"].strip():
                    continue
                seen.add(pair)
                yield {"anchor": query["statement"], "positive": premise["statement"],
                       "prover": query["prover"], "environment_id": query["environment_id"],
                       "context_id": query["context_id"], "declaration_id": pair[0], "positive_id": pair[1]}


def _message(role, value, chat):
    return [{"role": role, "content": value}] if chat else value


def _prompt_row(task, chat):
    return {"task_id": task.task_id, "environment_id": task.environment_id, "prover": task.prover,
            "prompt": _message("user", task_prompt(task, include_allowed_edits=False), chat)}


def _trajectories(paths, chat, emit, runtime_tasks):
    seen_episodes = {}
    seen_repairs, seen_answers = set(), set()
    tasks = {}
    labels = defaultdict(dict)
    for path in paths:
        for record in read_jsonl(path):
            episode = Episode.from_dict(record)
            key = (episode.task_id, episode.run_id)
            # A batched run can contain several tasks. Archived copies of the same task/run are duplicates.
            record_hash = digest(encode(record))
            if key in seen_episodes:
                if seen_episodes[key] != record_hash:
                    raise ValueError(f"conflicting episode records for task and run {key}")
                continue
            seen_episodes[key] = record_hash
            task = TaskSpec.from_dict(episode.task)
            prompt_text = task_prompt(task, include_allowed_edits=False)
            identity = {"task_id": task.task_id, "environment_id": task.environment_id, "prover": task.prover}
            common = {**identity, "prompt": _message("user", prompt_text, chat)}
            metadata = {**identity, "run_id": episode.run_id}
            if task.task_id not in tasks:
                tasks[task.task_id] = common
                if task.task_id not in runtime_tasks:
                    emit("grpo", common)
            final = VerificationEvidence.from_dict(episode.final_evidence)
            final_accepted = proof_reward(task, final).value == 1.0
            if final_accepted and (task.task_id, episode.final_candidate) not in seen_answers:
                seen_answers.add((task.task_id, episode.final_candidate))
                emit("sft", {**common, "run_id": episode.run_id,
                             "completion": _message("assistant", episode.final_candidate, chat)})

            previous = None
            for row in trajectory_rows((episode,)):
                evidence = VerificationEvidence.from_dict(row["evidence"])
                last_step = row["step"] == len(episode.transitions) - 1
                emit("trajectory", {**row, **metadata, "prompt": prompt_text, "evidence": evidence.to_dict(),
                                    "terminated": last_step and evidence.task_success is True,
                                    "truncated": last_step and evidence.task_success is not True})
                # Keep infrastructure and policy-only outcomes in the trajectory, outside native training labels.
                if (evidence.execution_outcome != "exited" or evidence.checker_outcome == "policy_rejected"
                        or row["reward"] is None):
                    previous = None
                    continue
                candidate = row["action"]["candidate"]
                accepted = row["reward"] == 1.0
                if accepted and not final_accepted:
                    previous = None
                    continue
                prior = labels[task.task_id].setdefault(candidate, (accepted, episode.run_id))
                if prior[0] != accepted:
                    raise ValueError(f"conflicting native labels for task {task.task_id}")
                if accepted and previous is not None and candidate != previous["action"]["candidate"]:
                    selected = (task.task_id, previous["action"]["candidate"], candidate)
                    if selected not in seen_repairs:
                        seen_repairs.add(selected)
                        observation = previous["observation"]
                        feedback = (observation["stdout"] + "\n" + observation["stderr"]).strip()
                        repair_prompt = (f"{prompt_text}\n\nPrevious attempt:\n{selected[1]}\n\n"
                                         f"Checker verdict: {observation['checker_outcome']}\n{feedback}\n\n"
                                         "Return a revised proof fragment.")
                        emit("repair", {**metadata, "prompt": _message("user", repair_prompt, chat),
                                        "completion": _message("assistant", candidate, chat), "step": row["step"]})
                previous = row if not accepted else None

    for task_id, attempts in labels.items():
        common = tasks[task_id]
        accepted = sorted(candidate for candidate, (label, _) in attempts.items() if label)
        for candidate, (label, run_id) in sorted(attempts.items()):
            emit("unpaired", {**common, "completion": _message("assistant", candidate, chat),
                              "label": label, "run_id": run_id})
            if not label and accepted:
                chosen = accepted[0]
                emit("preference", {**common, "chosen": _message("assistant", chosen, chat),
                                    "rejected": _message("assistant", candidate, chat),
                                    "chosen_run_id": attempts[chosen][1], "rejected_run_id": run_id})


def _proof_steps(paths):
    def state_row(state):
        return {"status": state.status, "state_id": state.state_id,
                "native_json": encode(state.native).decode("utf-8")}

    seen = {}
    for path in paths:
        for record in read_jsonl(path):
            episode = NativeProofEpisode.from_dict(record)
            task, run_id = episode.task, episode.manifest.run_id
            key = task.task_id, run_id
            record_hash = digest(encode(record))
            if key in seen:
                if record_hash != seen[key]:
                    raise ValueError(f"conflicting native proof episodes for task and run {key}")
                continue
            seen[key] = record_hash
            evidence = check_native_episode(episode)
            reward = proof_reward(task, evidence).value if evidence is not None else None
            finalization = episode.finalization
            assistance = {item.step: item.suggestion for item in episode.atp_progress}
            prompt = task_prompt(task, include_allowed_edits=False)
            before = state_row(episode.initial)
            for index, step in enumerate(episode.transitions):
                last = index == len(episode.transitions) - 1
                verified = last and evidence is not None
                successful = verified and evidence.task_success is True
                feedback = state_row(step.observation)
                atp = assistance.get(index)
                unresolved = None
                if last and episode.atp is not None:
                    if episode.atp.outcome == "accepted":
                        atp = episode.atp
                    else:
                        unresolved = episode.atp
                yield {"task_id": task.task_id, "environment_id": task.environment_id, "prover": task.prover,
                       "run_id": run_id, "step": index, "prompt": prompt, "before": before,
                       "action": step.action.to_dict(), "feedback": feedback, "committed": step.committed,
                       "reward": reward if verified and finalization.match != "same_locked_target" else None,
                       "terminated": successful, "truncated": last and not successful,
                       "stop_reason": episode.stop_reason if last else None,
                       "final_candidate": finalization.candidate if verified else None,
                       "final_match": finalization.match if verified else None,
                       "final_evidence": evidence.to_dict() if verified else None,
                       "atp_json": encode(atp.to_dict()).decode("utf-8") if atp is not None else None,
                       "unapplied_atp_json": encode(unresolved.to_dict()).decode("utf-8") if unresolved else None}
                if step.committed:
                    before = feedback


def export_training_data(output: Path, *, bundles=(), catalog: Path | None = None, episodes=(), native_episodes=(), locks=(),
                         task_manifest="completion.json",
                         format="jsonl", style="standard", split=None, exclude_source_hashes=()):
    """Create trainer views in a new directory and return their manifest."""
    if format not in {"jsonl", "parquet", "both"}:
        raise ValueError("format must be jsonl, parquet or both")
    if style not in {"standard", "chat"} or split not in {None, "train", "validation", "test"}:
        raise ValueError("invalid trainer style or split")
    excluded = set(exclude_source_hashes)
    if any(not SHA256.fullmatch(key) for key in excluded):
        raise ValueError("expected one lowercase SHA-256 per excluded source")
    libraries = ()
    if catalog is not None:
        from itpeval.corpus.library_collection import load_catalog

        libraries = load_catalog(catalog)
    catalog_bundles = [bundle for library in libraries for bundle in library.bundles]
    bundles = sorted({Path(path).resolve() for path in (*bundles, *catalog_bundles)})
    episodes = sorted({Path(path).resolve() for path in episodes})
    native_episodes = sorted({Path(path).resolve() for path in native_episodes})
    locks = sorted({Path(path).resolve() for path in locks})
    if not bundles and not episodes and not native_episodes and not locks:
        raise ValueError("pass at least one extraction bundle, episode file or environment lock")
    output = Path(output).absolute()
    if output.exists():
        raise FileExistsError(output)
    schemas = None
    if format in {"parquet", "both"}:
        try:
            schemas = _arrow_schemas(style == "chat")
        except ImportError as error:
            raise ValueError("Parquet export requires the itpeval[parquet] extra") from error
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as temp:
        stage = Path(temp) / "data"
        stage.mkdir()
        writers = {}
        counts = Counter()
        runtime_tasks = {}
        with ExitStack() as stack:
            def emit(view, row):
                if view not in writers:
                    writers[view] = stack.enter_context((stage / f"{view}.jsonl").open("wb"))
                writers[view].write(encode({"schema_version": 1, "split": split, **row}) + b"\n")
                counts[view] += 1

            for row in _sources(bundles, excluded):
                emit("pretraining", row)
            for row in _retrieval(bundles):
                emit("retrieval", row)
            for lock in locks:
                task = build_task(load_project(lock), task_manifest)
                if task.task_id not in runtime_tasks:
                    runtime_tasks[task.task_id] = {"lock_path": str(lock), "manifest_path": task_manifest,
                                                   "environment_id": task.environment_id, "prover": task.prover}
                    emit("grpo", _prompt_row(task, style == "chat"))
            _trajectories(episodes, style == "chat", emit, runtime_tasks)
            for row in _proof_steps(native_episodes):
                emit("proof_steps", row)

        if schemas is not None:
            for view in counts:
                jsonl = stage / f"{view}.jsonl"
                write_rows_parquet(jsonl, stage / f"{view}.parquet", schemas[view])
                if format == "parquet":
                    jsonl.unlink()
        manifest = {"schema_version": 1, "style": style, "format": format, "split": split,
                    "extraction_bundles": [path.name for path in bundles], "episode_files": len(episodes),
                    "views": {view: counts[view] for view in VIEWS if view != "proof_steps" or native_episodes}}
        if native_episodes:
            manifest["native_episode_files"] = len(native_episodes)
        if libraries:
            manifest["libraries"] = [
                {"name": library.name, "revision": library.revision, "license": library.license,
                 "bundles": [path.name for path in library.bundles]}
                for library in libraries
            ]
        if runtime_tasks:
            manifest["runtime_tasks"] = runtime_tasks
        (stage / "manifest.json").write_bytes(encode(manifest) + b"\n")
        stage.rename(output)
    return manifest


def add_arguments(parser):
    parser.add_argument("--bundle", type=Path, action="append", default=[], help="repeat for each native extraction bundle")
    parser.add_argument("--catalog", type=Path, help="library catalog of native extraction bundles")
    parser.add_argument("--episodes", type=Path, action="append", default=[], help="repeat for each episodes.jsonl file")
    parser.add_argument("--native-episodes", type=Path, action="append", default=[],
                        help="repeat for each goal/action episode JSONL file")
    parser.add_argument("--lock", type=Path, action="append", default=[], help="repeat for each local GRPO task environment")
    parser.add_argument("--task-manifest", default="completion.json", help="relative task manifest for the provided locks")
    parser.add_argument("--output", type=Path, required=True, help="new training export directory")
    parser.add_argument("--format", choices=("jsonl", "parquet", "both"), default="jsonl")
    parser.add_argument("--style", choices=("standard", "chat"), default="standard")
    parser.add_argument("--split", choices=("train", "validation", "test"), help="label these author-selected inputs")
    parser.add_argument("--exclude-source-hashes", type=Path, help="held-out SHA-256 hashes, one per line (pretraining)")


def run_command(args):
    exclude = args.exclude_source_hashes
    manifest = export_training_data(args.output, bundles=args.bundle, catalog=args.catalog,
                                    episodes=args.episodes, native_episodes=args.native_episodes, locks=args.lock,
                                    task_manifest=args.task_manifest, format=args.format, style=args.style, split=args.split,
                                    exclude_source_hashes=exclude.read_text().split() if exclude else ())
    print(json.dumps(manifest, sort_keys=True))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_arguments(parser)
    return run_command(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
