"""Build or validate the ten-prover statement export."""
from __future__ import annotations

import argparse
from pathlib import Path

from extended_inventory import build_extended


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build the ten-prover statement export.")
    parser.add_argument("--check", action="store_true", help="check deterministic exports without writing")
    args = parser.parse_args()
    build_extended(Path(__file__).resolve().parent.parent, check=args.check)
