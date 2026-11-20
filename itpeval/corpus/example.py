"""Export declarations and premise-selection tasks from a native project fixture."""

import argparse
from pathlib import Path

from itpeval.corpus.datasets import export_dataset as export
from itpeval.environments import prepare_project
from itpeval.extraction import ADAPTERS

LIBRARY = Path(__file__).resolve().parents[1] / "tests/fixtures/projects"
ENTRY = {"lean4": "Client.lean", "rocq": "Client.v", "acl2": "events.lisp", "agda": "Client.agda",
         "metamath": "client.mm", "mizar": "sample.miz", "isabelle": "Sample.thy",
         "hol-light": "sample.ml", "pvs": "sample.pvs", "hol4": "sampleScript.sml"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prover", choices=sorted(ADAPTERS), required=True)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--project", type=Path)
    parser.add_argument("--entrypoint")
    args = parser.parse_args()
    project = args.project or LIBRARY / args.prover / "library"
    entrypoint = args.entrypoint or ENTRY.get(args.prover)
    if not entrypoint:
        parser.error("specify the project entrypoint")
    prepared = prepare_project(args.prover, project, prefix=args.prefix, cache=args.cache)
    result, dataset = export(prepared, entrypoint, args.output)
    print(f"{result.report['declarations']} declarations in {result.path}")
    print(dataset)


if __name__ == "__main__":
    main()
