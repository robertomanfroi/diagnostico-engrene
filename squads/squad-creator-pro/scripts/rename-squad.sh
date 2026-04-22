#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE_SCRIPT="$SCRIPT_DIR/../../squad-creator/scripts/rename-squad.sh"

exec bash "$BASE_SCRIPT" "$@"
