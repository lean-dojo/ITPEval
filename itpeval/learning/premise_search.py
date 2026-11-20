"""A bounded Metamath search over visible assertions with the requested conclusion."""

from __future__ import annotations

import argparse
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, require_capabilities
from itpeval.core.episodes import Action
from itpeval.core.records import digest
from itpeval.corpus.datasets import match_target
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project
from itpeval.extraction import extract_project
from itpeval.learning.episodes import export_jsonl, replay
from itpeval.learning.manifests import RunManifest
from itpeval.learning.rollouts import rollout
from itpeval.retrieval import CorpusIndex

REQUIRES = {"inspect_declarations", "edit_document", "proof_completion"}


def search(prepared, cache: Path, output: Path, *, qualification_report=None):
    task = build_task(prepared)
    require_capabilities(task.prover, sorted(REQUIRES), prepared=prepared, qualification_report=qualification_report,
                         allow_experimental=qualification_report is None)
    if task.prover != "metamath":
        raise ValueError("this search requires the Metamath assertion and context extraction backend")
    bundle = extract_project(prepared, task.artifact.entrypoint, cache)
    target = match_target(bundle.path, task, prepared=prepared)
    contexts = {r["context_id"]: r for r in read_jsonl(bundle.path / "contexts.jsonl")}
    index = CorpusIndex(bundle.path / "index.sqlite")
    hits = index.search(target.statement, environment_id=prepared.environment_id,
                        context_id=target.context_id, limit=100)
    # The native verifier decides whether the active hypotheses satisfy the premise
    # and its disjoint-variable conditions. This search only tries direct applications.
    candidates = []
    retrieved = []
    for hit in hits:
        if hit["kind"] not in {"$p", "$a"} or hit["statement"] != target.statement:
            continue
        tokens = [*contexts[hit["context_id"]]["hypotheses"], hit["name"]]
        if all(token in task.proof_atoms for token in tokens):
            candidates.append(" ".join(tokens))
            retrieved.append(hit["declaration_id"])
    if not candidates:
        raise ValueError("no visible assertion has an eligible direct application")
    config = {"algorithm": "direct_assertion_application", "requires": sorted(REQUIRES),
              "retrieved": retrieved}
    manifest = RunManifest.for_proof_task(task, digest([bundle.path.name, target.declaration_id]),
                                          digest(target.statement), config, max_attempts=len(candidates))

    def choose(_, history):
        candidate = candidates[len(history)]
        return Action("edit_document", candidate, candidate)

    manifest.bind(output)
    episode = rollout(task, prepared, manifest, choose)
    export_jsonl([episode], output)
    return replay(episode, task=task, prepared=prepared)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", required=True, type=Path)
    parser.add_argument("--cache", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--qualification-report", type=Path, help="require exact environment/build qualification")
    args = parser.parse_args()
    prepared = prepare_project("metamath", curated_project("metamath"), prefix=args.prefix, cache=args.cache)
    result = search(prepared, args.cache / "extraction", args.output, qualification_report=args.qualification_report)
    print(f"{result.checker_outcome} {result.completion_status}")
    raise SystemExit(0 if result.task_success is True else 1)


if __name__ == "__main__":
    main()
