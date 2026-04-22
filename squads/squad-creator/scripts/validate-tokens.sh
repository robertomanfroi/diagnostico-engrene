#!/bin/bash
# validate-tokens.sh — SINKRA Token Reconciliation Validator
# Validates that tokens declared in process-token-map.yaml are consistent
# with tokens consumed/produced across workflows and tasks.
#
# Usage: bash scripts/validate-tokens.sh [squad-path]
# Exit codes: 0 = PASS, 1 = FAIL, 2 = WARN

set -euo pipefail

SQUAD_PATH="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
TOKEN_MAP="$SQUAD_PATH/data/process-token-map.yaml"
CONTRACT="$SQUAD_PATH/data/base-core-contract.yaml"
WORKFLOWS_DIR="$SQUAD_PATH/workflows"
TASKS_DIR="$SQUAD_PATH/tasks"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

errors=0
warnings=0
checks=0

log_pass() { checks=$((checks + 1)); echo -e "  ${GREEN}✓${NC} $1"; }
log_fail() { checks=$((checks + 1)); errors=$((errors + 1)); echo -e "  ${RED}✗${NC} $1"; }
log_warn() { checks=$((checks + 1)); warnings=$((warnings + 1)); echo -e "  ${YELLOW}⚠${NC} $1"; }

echo "══════════════════════════════════════════════════════════"
echo "  SINKRA Token Reconciliation Validator"
echo "  Squad: $(basename "$SQUAD_PATH")"
echo "  Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "══════════════════════════════════════════════════════════"
echo ""

# --- Check 1: Token map exists ---
echo "Phase 1: File Existence"
if [ -f "$TOKEN_MAP" ]; then
  log_pass "process-token-map.yaml exists"
else
  log_fail "process-token-map.yaml NOT FOUND"
  echo ""
  echo "RESULT: FAIL ($errors errors)"
  exit 1
fi

if [ -f "$CONTRACT" ]; then
  log_pass "base-core-contract.yaml exists"
else
  log_warn "base-core-contract.yaml not found (reconciliation source missing)"
fi

# --- Check 2: Token count ---
echo ""
echo "Phase 2: Token Inventory"
declared_count=$(grep -c "token_name:" "$TOKEN_MAP" 2>/dev/null || echo 0)
if [ "$declared_count" -eq 19 ]; then
  log_pass "Token count matches contract: $declared_count/19"
else
  log_fail "Token count mismatch: found $declared_count, expected 19"
fi

# --- Check 3: Producer contract IDs are sequential ---
echo ""
echo "Phase 3: Producer Contract Integrity"
producer_ids=$(grep "producer_contract_id:" "$TOKEN_MAP" | sed 's/.*: //' | sort)
expected_ids=""
for i in $(seq -w 1 19); do
  expected_ids="${expected_ids}scb-atm-0${i}
"
done
# Normalize for comparison
producer_sorted=$(echo "$producer_ids" | tr -d ' ' | sort)
expected_sorted=$(echo "$expected_ids" | tr -d ' ' | grep -v '^$' | sort)

missing_producers=$(comm -23 <(echo "$expected_sorted") <(echo "$producer_sorted") 2>/dev/null || true)
if [ -z "$missing_producers" ]; then
  log_pass "All 19 producer contract IDs present (scb-atm-001 to scb-atm-019)"
else
  log_fail "Missing producer IDs: $missing_producers"
fi

# --- Check 4: No orphan consumed_by references ---
echo ""
echo "Phase 4: Consumer Chain Validation"
all_producers=$(grep "producer_contract_id:" "$TOKEN_MAP" | sed 's/.*: //' | tr -d ' ')
all_consumers=$(grep -oE 'scb-atm-[0-9]+' "$TOKEN_MAP" | sort -u)

orphan_consumers=""
for consumer in $all_consumers; do
  if ! echo "$all_producers" | grep -q "^${consumer}$"; then
    orphan_consumers="${orphan_consumers} ${consumer}"
  fi
done

if [ -z "$orphan_consumers" ]; then
  log_pass "All consumed_by references resolve to valid producers"
else
  log_fail "Orphan consumer references:$orphan_consumers"
fi

# --- Check 5: Terminal tokens have empty consumed_by ---
echo ""
echo "Phase 5: Terminal Token Validation"
terminal_count=$(grep -A1 "consumed_by: \[\]" "$TOKEN_MAP" | grep -c "token_name:" 2>/dev/null || echo 0)
# base_handoff_token should be terminal
if grep -q "base_handoff_token" "$TOKEN_MAP" && grep -A3 "base_handoff_token" "$TOKEN_MAP" | grep -q "consumed_by: \[\]"; then
  log_pass "base_handoff_token is terminal (consumed_by: [])"
else
  log_warn "base_handoff_token may not be properly terminal"
fi

# --- Check 6: Token domains are valid ---
echo ""
echo "Phase 6: Domain Validation"
valid_domains="Strategic Tactical Operational"
invalid_domains=$(grep "domain:" "$TOKEN_MAP" | sed 's/.*domain: //' | tr -d ' ' | sort -u | while read -r domain; do
  if ! echo "$valid_domains" | grep -qw "$domain"; then
    echo "$domain"
  fi
done)

if [ -z "$invalid_domains" ]; then
  log_pass "All token domains are valid (Strategic/Tactical/Operational)"
else
  log_fail "Invalid domains found: $invalid_domains"
fi

# --- Check 7: Workflows reference tasks that exist ---
echo ""
echo "Phase 7: Workflow-Task Cross-Reference"
workflow_task_refs=$(grep -rh "task_ref:" "$WORKFLOWS_DIR" 2>/dev/null | sed 's/.*task_ref: //' | tr -d ' "' | sed 's/\.md$//' | sort -u)
missing_tasks=""
for task_ref in $workflow_task_refs; do
  if [ ! -f "$TASKS_DIR/${task_ref}.md" ]; then
    missing_tasks="${missing_tasks} ${task_ref}"
  fi
done

if [ -z "$missing_tasks" ]; then
  log_pass "All workflow task_refs resolve to existing task files"
else
  log_fail "Missing task files:$missing_tasks"
fi

# --- Check 8: No .md in task_ref values ---
echo ""
echo "Phase 8: task_ref Format Compliance"
bad_refs=$(grep -rn "task_ref:.*\.md" "$WORKFLOWS_DIR" 2>/dev/null || true)
if [ -z "$bad_refs" ]; then
  log_pass "No task_ref values contain .md extension"
else
  log_fail "task_ref with .md extension found:"
  echo "$bad_refs" | head -5
fi

# --- Summary ---
echo ""
echo "══════════════════════════════════════════════════════════"
echo "  RESULTS"
echo "══════════════════════════════════════════════════════════"
echo "  Checks: $checks"
echo "  Passed: $((checks - errors - warnings))"
echo "  Warnings: $warnings"
echo "  Errors: $errors"
echo ""

if [ "$errors" -gt 0 ]; then
  echo -e "  Verdict: ${RED}FAIL${NC}"
  exit 1
elif [ "$warnings" -gt 0 ]; then
  echo -e "  Verdict: ${YELLOW}WARN${NC} (non-blocking)"
  exit 2
else
  echo -e "  Verdict: ${GREEN}PASS${NC}"
  exit 0
fi
