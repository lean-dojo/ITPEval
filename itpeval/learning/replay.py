"""Replay one exported episode against a reviewed local task and export a trainer view."""

import argparse
import json
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.core.episodes import Episode
from itpeval.environments import load_project
from itpeval.learning.episodes import export_jsonl, replay


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("episode", type=Path, help="one episode JSONL row")
    parser.add_argument("--lock", required=True, type=Path)
    parser.add_argument("--manifest", default="completion.json")
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--export", type=Path)
    parser.add_argument("--view", choices=["attempts", "supervised", "repair", "trajectory"], default="attempts")
    args = parser.parse_args(argv)
    paths = [args.episode, args.receipt] + ([args.export] if args.export else [])
    if len({path.resolve() for path in paths}) != len(paths):
        parser.error("episode, receipt and export paths must be distinct")
    episode = Episode.from_dict(json.loads(args.episode.read_bytes()))
    prepared = load_project(args.lock)
    final = replay(episode, task=build_task(prepared, args.manifest), prepared=prepared, receipt=args.receipt)
    if args.export:
        export_jsonl([episode], args.export, view=args.view)
    print(json.dumps({"execution_outcome": final.execution_outcome, "checker_outcome": final.checker_outcome,
                      "task_success": final.task_success, "receipt": str(args.receipt)}))


if __name__ == "__main__":
    main()
