"""Measure fresh and verified-base checking of the packaged Metamath project."""
import argparse
import json
from pathlib import Path

from itpeval.tests.conformance.metamath_base import measure


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    for name in ("prefix", "cache", "output"):
        cli.add_argument("--" + name, type=Path, required=True)
    args = cli.parse_args()
    args.output.write_text(json.dumps(measure(args.prefix, args.cache), indent=2) + "\n")
