"""Check and extract Words.lean using a built CSLib checkout and its Lake dependencies."""
import argparse
import json
from pathlib import Path

from itpeval.core.types import Artifact, TaskSpec
from itpeval.environments import prepare_project
from itpeval.extraction import extract_project
from itpeval.verification import verify


def check_and_extract(project: Path, cslib: Path, prefix: Path, output: Path):
    build_dir = Path(".lake/build/lib/lean")

    # Lock compiled modules from the same build, including indirect imports.
    libraries = {"cslib": cslib / build_dir}
    packages = cslib / ".lake/packages"
    libraries.update({p.name: p / build_dir for p in packages.iterdir() if (p / build_dir).is_dir()})
    env = prepare_project("lean4", project, prefix=prefix, cache=output / "cache", libraries=libraries)

    # Check the complete file against the locked environment.
    name = "Words.lean"
    artifact = Artifact.from_files(name, {name: (env.project / name).read_bytes()})
    task = TaskSpec("lean4", env.environment_id, "check_artifact", artifact)
    evidence = verify(task, prepared=env)
    print(evidence.checker_outcome)
    if evidence.checker_outcome != "accepted":
        raise RuntimeError(evidence.stderr or evidence.stdout)

    # Extract the declarations defined by the client.
    result = extract_project(env, name, output / "extracted")
    for row in (result.path / "declarations.jsonl").read_text().splitlines():
        print(json.loads(row)["name"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cslib", type=Path, required=True, help="built CSLib checkout")
    parser.add_argument("--prefix", type=Path, required=True, help="prefix containing the matching lean4/bin/lean")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent / "project",
                        help="directory containing Words.lean")
    args = parser.parse_args()
    check_and_extract(args.project, args.cslib, args.prefix, args.output)


if __name__ == "__main__":
    main()
