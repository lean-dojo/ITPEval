"""Exercise native search and checked episode replay on five proof assistants."""

import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from time import perf_counter

from itpeval.backends.registry import curated_project, get_backend
from itpeval.corpus.storage import jsonl
from itpeval.environments import prepare_project
from itpeval.environments.cache import write_json
from itpeval.learning.manifests import RunManifest
from itpeval.learning.native_proofs import NativeProofEpisode, SearchWithATP, replay_native_episode, rollout_native
from itpeval.learning.training_data import export_training_data
from itpeval.runtime.proof_driver import NativeProofAction, NativeProofDriver


CASES = {
    "acl2": ("acl2", "automation", "completion.json", ("promote",), 2),
    "agda": ("agda", "auto", "completion.json", (), 1),
    "agda-hint": ("agda", "auto", "right-zero.json", (), 1),
    "metamath": ("metamath", "completion", "completion.json", (), 3),
    "mizar": ("mizar", "justifications", "completion.json", (), 1),
    "pvs": ("pvs", "grind", "completion.json", ("(skosimp)", "(split)"), 2),
}


def exercise(name, args):
    prover, directory, manifest_path, commands, searches = CASES[name]
    root = curated_project(prover).parent / directory
    prepared = prepare_project(prover, root, prefix=args.prefix, cache=args.cache)
    task = get_backend(prover).build_task(prepared, manifest_path)
    hints = ("plus-zero",) if name == "agda-hint" else ()
    finish = "(then (skosimp) (split) (grind))" if prover == "pvs" else None
    decisions = [NativeProofAction("command", command) for command in commands]
    decisions.extend(SearchWithATP(hints=hints) for _ in range(searches))
    run = RunManifest.for_native_proof_task(task, "native-search-fixtures", name, {"hints": list(hints)},
                                           max_attempts=len(decisions))
    start = perf_counter()
    episode = rollout_native(task, prepared, run, lambda _task, _state, history: decisions[len(history)],
                             proof_fragment=finish)
    duration = perf_counter() - start
    loaded = NativeProofEpisode.from_dict(json.loads(json.dumps(episode.to_dict())))
    replay = replay_native_episode(loaded, task=task, prepared=prepared)
    assert replay is not None and replay.task_success is True
    assert episode.atp.outcome == "accepted" and len(episode.atp_progress) == searches - 1
    assert len(episode.transitions) == len(decisions)
    progress = [item.suggestion for item in episode.atp_progress]
    if prover == "metamath":
        assert [action.text for action in progress[0].evidence.plan] == ["distinct", "vx", "vy"]
        assert progress[0].verification is None and progress[0].evidence.trials[-1].verification.task_success is True
    if prover == "pvs":
        assert episode.finalization.match == "same_locked_target"
        assert dict(replay.obligations)["twice_TCC1"] == "discharged"
    if prover == "acl2":
        assert [(trial.action.text, trial.outcome) for trial in episode.atp.evidence.trials] == [
            ("s", "rejected"), ("bash", "accepted")]
    if prover == "mizar":
        assert [(trial.action.text, trial.outcome) for trial in episode.atp.evidence.trials] == [
            ("by TARSKI:2", "rejected"), ("by Th1", "accepted")]
    if prover == "agda":
        assert episode.atp.evidence.probe["hints"] == list(hints)

    driver = NativeProofDriver(task, prepared)
    for decision in decisions[:len(commands)]:
        driver.advance(decision)
    destination = args.work / name
    write_json(destination / "checkpoint.json", driver.checkpoint().to_dict())
    write_json(destination / "lock-reference.json", {"lock": str(prepared.lock_path), "manifest": manifest_path})
    if finish:
        (destination / "proof-fragment.txt").write_text(finish + "\n", encoding="utf-8")
    print(name, len(episode.transitions), replay.checker_outcome, flush=True)
    return episode, {"name": name, "prover": prover, "prover_build": prepared.spec.prover_build,
                     "task_id": task.task_id, "environment_id": task.environment_id, "rollout_s": duration,
                     "verification": replay.to_dict(), "match": episode.finalization.match,
                     "searches": [entry.to_dict() for entry in (*progress, episode.atp)],
                     "operations": {"atp_from_state": True, "automated_search": True}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "work", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda name: exercise(name, args), CASES))
    episodes = args.work / "episodes.jsonl"
    jsonl(episodes, (episode.to_dict() for episode, _ in results))
    export = export_training_data(args.work / "training", native_episodes=(episodes,), format="both")
    assert export["views"]["proof_steps"] == sum(len(episode.transitions) for episode, _ in results)
    write_json(args.output, [row for _, row in results])


if __name__ == "__main__":
    main()
