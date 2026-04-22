#!/usr/bin/env bash
set -euo pipefail

report_path="${1:-}"

if [[ -z "$report_path" ]]; then
  echo "usage: publish-benchmark-report.sh <report-path>" >&2
  exit 1
fi

if [[ ! -f "$report_path" ]]; then
  echo "report not found: $report_path" >&2
  exit 1
fi

echo "published_report=$report_path"
