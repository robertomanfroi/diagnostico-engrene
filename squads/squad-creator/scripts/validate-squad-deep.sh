#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════════════════════════
# VALIDATE-SQUAD-DEEP.SH - Deep Review Script (multi-runtime)
# ═══════════════════════════════════════════════════════════════════════════════
# Version: 1.0.0
# Compatibility: bash 3.2+ (macOS compatible)
# Purpose: Runtime-based deep quality analysis (Phases 4-6 from validate-squad.sh)
# Usage: ./validate-squad-deep.sh <squad-path> [--model quality|fast|<name>] [--verbose]
#
# This script requires at least one supported runtime. If none is available,
# it exits gracefully with a SKIPPED status JSON.
#
# Exit codes:
#   0 = Analysis complete
#   1 = Analysis failed
#   2 = Error (invalid input)
# ═══════════════════════════════════════════════════════════════════════════════

set -uo pipefail

# Force C locale for numeric operations
export LC_NUMERIC=C

# ═══════════════════════════════════════════════════════════════════════════════
# RUNTIME SETUP — shared infrastructure
# ═══════════════════════════════════════════════════════════════════════════════

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
RUNNER_LIB_DIR="$WORKSPACE_ROOT/infrastructure/scripts/runner-lib"
HAS_RUNNER_LIB="false"

if [[ -f "$RUNNER_LIB_DIR/loader.sh" ]]; then
  source "$RUNNER_LIB_DIR/loader.sh"
  HAS_RUNNER_LIB="true"
fi

# Runtime selection (default: claude, overridable by caller via env)
SELECTED_RUNTIME="${SELECTED_RUNTIME:-claude}"
LLM_TIMEOUT_SECONDS="${LLM_TIMEOUT_SECONDS:-3600}"
RETRY_MAX_ATTEMPTS="${RETRY_MAX_ATTEMPTS:-2}"
RETRY_BASE_DELAY_SECONDS="${RETRY_BASE_DELAY_SECONDS:-3}"
export SELECTED_RUNTIME LLM_TIMEOUT_SECONDS RETRY_MAX_ATTEMPTS RETRY_BASE_DELAY_SECONDS

# Check if at least one runtime CLI exists
_has_any_runtime() {
  command -v claude &>/dev/null || command -v codex &>/dev/null || command -v gemini &>/dev/null
}

if ! _has_any_runtime; then
  echo '{"phase": "deep", "status": "SKIPPED", "reason": "no LLM runtime found (claude/codex/gemini)", "score": null}'
  exit 0
fi

# If runner-lib loaded, auto-detect best runtime
if [[ "$HAS_RUNNER_LIB" == "true" ]]; then
  SELECTED_RUNTIME="$(detect_runtime "${SELECTED_RUNTIME:-auto}")"
fi

# ═══════════════════════════════════════════════════════════════════════════════
# ARGUMENT PARSING
# ═══════════════════════════════════════════════════════════════════════════════

SQUAD_PATH="${1:-.}"
MODEL_QUALITY=""
VERBOSE=false
FINDINGS_FILE=""

shift || true
while [[ $# -gt 0 ]]; do
  case $1 in
    --model)
      MODEL_QUALITY="${2:-}"
      shift 2
      ;;
    --verbose|-v)
      VERBOSE=true
      shift
      ;;
    --findings)
      FINDINGS_FILE="${2:-}"
      shift 2
      ;;
    *)
      shift
      ;;
  esac
done

if [[ -z "$MODEL_QUALITY" ]]; then
  if declare -f get_quality_model >/dev/null 2>&1; then
    MODEL_QUALITY="$(get_quality_model "$SELECTED_RUNTIME")"
  else
    case "$SELECTED_RUNTIME" in
      claude) MODEL_QUALITY="opus" ;;
      codex)  MODEL_QUALITY="gpt-5.4" ;;
      gemini) MODEL_QUALITY="gemini-3.1-pro-preview" ;;
      *)      MODEL_QUALITY="opus" ;;
    esac
  fi
fi

# Resolve to absolute path
if [[ ! "$SQUAD_PATH" = /* ]]; then
  SQUAD_PATH="$(cd "$SQUAD_PATH" 2>/dev/null && pwd)" || {
    echo '{"phase": "deep", "status": "ERROR", "reason": "Invalid squad path", "score": null}'
    exit 2
  }
fi

if [[ ! -d "$SQUAD_PATH" ]]; then
  echo "{\"phase\": \"deep\", \"status\": \"ERROR\", \"reason\": \"Squad directory not found: $SQUAD_PATH\", \"score\": null}"
  exit 2
fi

SQUAD_NAME="$(basename "$SQUAD_PATH")"

# ═══════════════════════════════════════════════════════════════════════════════
# COLLECT SQUAD CONTEXT
# ═══════════════════════════════════════════════════════════════════════════════

# Read config.yaml
config_content=""
[[ -f "$SQUAD_PATH/config.yaml" ]] && config_content=$(cat "$SQUAD_PATH/config.yaml" 2>/dev/null || true)

# Find entry agent
entry_agent=""
if [[ -f "$SQUAD_PATH/config.yaml" ]]; then
  entry_agent=$(grep "entry_agent:" "$SQUAD_PATH/config.yaml" 2>/dev/null | head -1 | sed 's/.*entry_agent:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs 2>/dev/null || true)
fi

# Read entry agent content
agent_content=""
sample_agent=""
if [[ -n "$entry_agent" ]] && [[ -f "$SQUAD_PATH/agents/${entry_agent}.md" ]]; then
  sample_agent="$SQUAD_PATH/agents/${entry_agent}.md"
fi
if [[ -z "$sample_agent" ]]; then
  sample_agent=$(find "$SQUAD_PATH/agents" -name "*.md" 2>/dev/null | head -1)
fi
[[ -f "$sample_agent" ]] && agent_content=$(cat "$sample_agent" 2>/dev/null || true)

# Read first workflow
workflow_content=""
sample_workflow=$(find "$SQUAD_PATH/workflows" -name "*.yaml" -o -name "*.yml" 2>/dev/null | head -1)
[[ -f "$sample_workflow" ]] && workflow_content=$(cat "$sample_workflow" 2>/dev/null || true)

# Collect basic metrics
agent_count=$(find "$SQUAD_PATH/agents" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
task_count=$(find "$SQUAD_PATH/tasks" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
checklist_count=$(find "$SQUAD_PATH/checklists" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
total_lines=$(find "$SQUAD_PATH" -type f \( -name "*.md" -o -name "*.yaml" \) -exec cat {} + 2>/dev/null | wc -l | tr -d ' ')

# ═══════════════════════════════════════════════════════════════════════════════
# TRUNCATION SAFETY
# ═══════════════════════════════════════════════════════════════════════════════

config_len=${#config_content}
agent_len=${#agent_content}
workflow_len=${#workflow_content}
max_content=15000

if [[ $((config_len + agent_len + workflow_len)) -gt $max_content ]]; then
  remaining=$((max_content - config_len))
  if [[ $remaining -lt 1000 ]]; then
    remaining=1000
  fi
  agent_max=$((remaining * 70 / 100))
  wf_max=$((remaining * 30 / 100))
  if [[ $agent_len -gt $agent_max ]]; then
    agent_content="${agent_content:0:$agent_max}

... [TRUNCATED at $agent_max chars] ..."
  fi
  if [[ $workflow_len -gt $wf_max ]]; then
    workflow_content="${workflow_content:0:$wf_max}

... [TRUNCATED at $wf_max chars] ..."
  fi
fi

# ═══════════════════════════════════════════════════════════════════════════════
# BUILD ANALYSIS PROMPT
# ═══════════════════════════════════════════════════════════════════════════════

ANALYSIS_PROMPT="You are a senior squad quality auditor for the AIOX framework. Perform a deep dimensional analysis.

IMPORTANT: Respond with ONLY valid JSON. No markdown, no explanation, no code fences.
IMPORTANT: Keep the JSON keys exactly as requested below.
IMPORTANT: Write every human-readable value in English. This JSON is the canonical internal analysis artifact.

## Squad: $SQUAD_NAME
Agents: $agent_count | Tasks: $task_count | Checklists: $checklist_count | Lines: $total_lines

## config.yaml (FULL):
\`\`\`yaml
$config_content
\`\`\`

## Entry Agent — $(basename "${sample_agent:-unknown}") (FULL):
\`\`\`markdown
$agent_content
\`\`\`

## First Workflow (FULL):
\`\`\`yaml
$workflow_content
\`\`\`

## Previous Phase Findings (deterministic — already validated)
$(if [[ -n "$FINDINGS_FILE" && -f "$FINDINGS_FILE" ]]; then cat "$FINDINGS_FILE"; else echo "(no previous findings injected)"; fi)

## Analysis Instructions

Score each dimension 0-10. Be STRICT -- a score of 7+ means production-ready quality.
Use the Previous Phase Findings above as ground truth — do not re-evaluate what was already checked deterministically.

## Required JSON Response:
{
  \"structural_completeness\": {
    \"score\": 5,
    \"items\": [{\"item\": \"tested flag\", \"status\": \"PASS or FAIL\", \"detail\": \"...\"}]
  },
  \"security_audit\": {
    \"score\": 8,
    \"false_positive_count\": 0,
    \"real_issue_count\": 0,
    \"checks\": [{\"id\": \"SEC-001\", \"status\": \"PASS or FALSE_POSITIVE or FAIL\", \"detail\": \"...\"}]
  },
  \"workflow_analysis\": {
    \"score\": 7,
    \"dimensions\": [{\"name\": \"coherence\", \"score\": 9, \"detail\": \"...\"}]
  },
  \"agent_quality\": {
    \"score\": 5,
    \"criteria\": [{\"name\": \"smoke_tests\", \"status\": \"PASS or PARTIAL or FAIL\", \"detail\": \"...\"}]
  },
  \"squad_agnosticism\": {
    \"score\": 8,
    \"violations\": [{\"item\": \"...\", \"detail\": \"...\"}]
  },
  \"config_quality\": {
    \"score\": 7,
    \"fields\": [{\"name\": \"distribution_contract\", \"status\": \"PASS or WARN or FAIL\"}]
  },
  \"production_evidence\": {
    \"score\": 6,
    \"signals\": [{\"name\": \"runtime_evidence\", \"status\": \"PASS or FAIL\", \"detail\": \"...\"}]
  },
  \"executive_summary\": {
    \"overall_score\": 5.8,
    \"verdict\": \"PASS or CONDITIONAL or FAIL\",
    \"priority_fixes\": [\"1. ...\", \"2. ...\", \"3. ...\"],
    \"strengths\": [\"...\"],
    \"improvements\": [\"...\"]
  }
}"

# ═══════════════════════════════════════════════════════════════════════════════
# RUN CLAUDE CLI
# ═══════════════════════════════════════════════════════════════════════════════

prompt_file=$(mktemp "${TMPDIR:-/tmp}/validate-squad-deep-prompt.XXXXXX")
printf '%s' "$ANALYSIS_PROMPT" > "$prompt_file"

if [[ "$VERBOSE" == "true" ]]; then
  echo "Running deep analysis with $SELECTED_RUNTIME ($MODEL_QUALITY)..." >&2
  echo "Prompt size: $(wc -c < "$prompt_file" | tr -d ' ') bytes" >&2
fi

claude_output=""
if [[ "$HAS_RUNNER_LIB" == "true" ]]; then
  # Use shared runner-lib (supports Claude/Codex/Gemini + fallback + metrics)
  tmp_out=$(mktemp)
  PHASE_MAX_TURNS=""
  PHASE_ALLOWED_TOOLS=""
  if _exec_runtime "$MODEL_QUALITY" "$prompt_file" "$tmp_out" 2>/dev/null; then
    claude_output=$(cat "$tmp_out")
    rm -f "$tmp_out"
  else
    rm -f "$tmp_out"
    claude_output=""
  fi
else
  # Fallback: direct claude -p
  claude_output=$(claude -p --model "$MODEL_QUALITY" --dangerously-skip-permissions < "$prompt_file" 2>&1) || true
fi
if [[ -n "$claude_output" ]]; then
  rm -f "$prompt_file"

  # Extract the first JSON object from the output
  json_result=$(printf "%s" "$claude_output" | python3 -c '
import json, sys, re

text = sys.stdin.read()
text = re.sub(r"\x1B(?:[@-Z\\\\-_]|\[[0-?]*[ -/]*[@-~])", "", text)
text = text.replace("```json", "```").replace("```JSON", "```")

decoder = json.JSONDecoder()
for i, c in enumerate(text):
    if c != "{":
        continue
    try:
        obj, end = decoder.raw_decode(text, i)
        print(json.dumps(obj))
        sys.exit(0)
    except json.JSONDecodeError:
        continue
print("{}")
' 2>/dev/null || echo '{}')

  # Wrap in phase envelope
  echo "{\"phase\": \"deep\", \"status\": \"REVIEWED\", \"analysis\": $json_result}"
else
  rm -f "$prompt_file"
  echo '{"phase": "deep", "status": "FAILED", "reason": "Claude CLI analysis failed", "score": null}'
  exit 1
fi
