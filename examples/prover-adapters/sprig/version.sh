#!/usr/bin/env bash
set -eu
exec "${ITPEVAL_PYTHON:-python3}" "$(dirname "$0")/sprig.py" --version
