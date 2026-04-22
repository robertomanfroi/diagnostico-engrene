#!/usr/bin/env bash
set -euo pipefail

subject_a="${1:-}"
subject_b="${2:-}"

if [[ -z "$subject_a" || -z "$subject_b" ]]; then
  echo "usage: prepare-benchmark-workspace.sh <subject-a> <subject-b>" >&2
  exit 1
fi

mkdir -p "docs/bench/${subject_a}-vs-${subject_b}"
mkdir -p "outputs/sinkra-squad/spy"
echo "workspace_ready=true"
