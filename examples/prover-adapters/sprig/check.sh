#!/usr/bin/env bash
set -eu
adapter=$(cd "$(dirname "$0")" && pwd)
task_dir=${ITPEVAL_TASK_DIR:-"$adapter/hello"}
exec "${ITPEVAL_PYTHON:-python3}" "$adapter/sprig.py" check \
  "$task_dir/problem.json" "$task_dir/${ITPEVAL_TASK_FILE:-proof.json}"
