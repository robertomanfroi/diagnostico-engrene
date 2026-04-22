#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════════════════════════
# RENAME-SQUAD.SH - Automated Squad Rename Script
# ═══════════════════════════════════════════════════════════════════════════════
# Version: 1.0.0
# Compatibility: bash 3.2+ (macOS compatible, uses sed -i '')
# Purpose: Rename a squad across ALL repo surfaces atomically
# Usage: ./rename-squad.sh <old-name> <new-name> [--dry-run] [--no-branch]
#
# Phases:
#   1. BLAST RADIUS MAPPING — grep exaustivo, contagem de arquivos
#   2. RENAME ESTRUTURAL — git mv, config/squad yaml, scripts internos
#   3. PROPAGAÇÃO — sed replace em mirrors, cross-squad, workspace, infra, apps
#   4. VALIDAÇÃO — grep residual, validate-squad
#
# Exit codes:
#   0 = SUCCESS
#   1 = VALIDATION FAILED (residual refs or validate-squad fail)
#   2 = ERROR (invalid input, missing squad, etc.)
# ═══════════════════════════════════════════════════════════════════════════════

set -uo pipefail

# ─── Colors ───
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# ─── Args ───
OLD_NAME="${1:-}"
NEW_NAME="${2:-}"
DRY_RUN=false
NO_BRANCH=false

for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=true ;;
    --no-branch) NO_BRANCH=true ;;
  esac
done

# ─── Paths ───
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
SQUADS_DIR="$ROOT/squads"

# ─── Helpers ───
log_info()  { echo -e "${CYAN}[INFO]${NC} $1"; }
log_pass()  { echo -e "${GREEN}  ✓${NC} $1"; }
log_fail()  { echo -e "${RED}  ✗${NC} $1"; }
log_warn()  { echo -e "${YELLOW}  ⚠${NC} $1"; }
log_phase() { echo -e "\n${BOLD}${BLUE}═══ $1 ═══${NC}"; }

# ─── PascalCase converter ───
to_pascal() {
  echo "$1" | sed 's/-/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2)}1' | tr -d ' '
}

# ─── Validation ───
if [[ -z "$OLD_NAME" || -z "$NEW_NAME" ]]; then
  echo -e "${BOLD}Usage:${NC} rename-squad.sh <old-name> <new-name> [--dry-run] [--no-branch]"
  echo ""
  echo "  --dry-run    Show blast radius without making changes"
  echo "  --no-branch  Skip branch creation (use current branch)"
  echo ""
  echo "Examples:"
  echo "  rename-squad.sh old-name new-name"
  echo "  rename-squad.sh old-name new-name --dry-run"
  exit 2
fi

if [[ ! -d "$SQUADS_DIR/$OLD_NAME" ]]; then
  log_fail "Squad '$OLD_NAME' not found at $SQUADS_DIR/$OLD_NAME"
  exit 2
fi

if [[ -d "$SQUADS_DIR/$NEW_NAME" ]]; then
  log_fail "Squad '$NEW_NAME' already exists at $SQUADS_DIR/$NEW_NAME"
  exit 2
fi

OLD_PASCAL=$(to_pascal "$OLD_NAME")
NEW_PASCAL=$(to_pascal "$NEW_NAME")

echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║         RENAME-SQUAD v1.0 — Automated Squad Rename          ║${NC}"
echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "  Old name: ${RED}$OLD_NAME${NC} (PascalCase: $OLD_PASCAL)"
echo -e "  New name: ${GREEN}$NEW_NAME${NC} (PascalCase: $NEW_PASCAL)"
if $DRY_RUN; then
  echo -e "  Mode: ${YELLOW}DRY-RUN (no changes)${NC}"
fi

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 1: BLAST RADIUS MAPPING
# ═══════════════════════════════════════════════════════════════════════════════
log_phase "PHASE 1: Blast Radius Mapping"

EXTENSIONS="--include=*.md --include=*.yaml --include=*.yml --include=*.cjs --include=*.js --include=*.ts --include=*.tsx --include=*.sh --include=*.mdc --include=*.json"

# Count refs by zone
count_refs() {
  local pattern="$1"
  local path="$2"
  grep -r "$pattern" $EXTENSIONS -l "$path" 2>/dev/null | grep -v node_modules | grep -v ".git/" | wc -l | tr -d ' '
}

TOTAL_SQUAD=$(count_refs "squads/$OLD_NAME" "$SQUADS_DIR/$OLD_NAME")
TOTAL_CLAUDE=$(count_refs "$OLD_NAME" "$ROOT/.claude" 2>/dev/null || echo 0)
TOTAL_CODEX=0  # .codex/skills removed; skills now in .agents/skills
TOTAL_GEMINI=$(count_refs "$OLD_NAME" "$ROOT/.gemini" 2>/dev/null || echo 0)
TOTAL_AGENTS=$(count_refs "$OLD_NAME" "$ROOT/.agents" 2>/dev/null || echo 0)
TOTAL_CURSOR=$(count_refs "$OLD_NAME" "$ROOT/.cursor" 2>/dev/null || echo 0)
TOTAL_CROSSSQUAD=$(grep -r "squads/$OLD_NAME" $EXTENSIONS -l "$SQUADS_DIR" 2>/dev/null | grep -v "$SQUADS_DIR/$OLD_NAME" | wc -l | tr -d ' ')
TOTAL_WORKSPACE=$(count_refs "$OLD_NAME" "$ROOT/workspace" 2>/dev/null || echo 0)
TOTAL_INFRA=$(count_refs "$OLD_NAME" "$ROOT/infrastructure" 2>/dev/null || echo 0)
TOTAL_APPS=$(count_refs "$OLD_NAME" "$ROOT/apps" 2>/dev/null || echo 0)
TOTAL_DOCS=$(count_refs "squads/$OLD_NAME" "$ROOT/docs" 2>/dev/null || echo 0)
TOTAL_CORE=$(count_refs "$OLD_NAME" "$ROOT/.aiox-core" 2>/dev/null || echo 0)

GRAND_TOTAL=$((TOTAL_SQUAD + TOTAL_CLAUDE + TOTAL_CODEX + TOTAL_GEMINI + TOTAL_AGENTS + TOTAL_CURSOR + TOTAL_CROSSSQUAD + TOTAL_WORKSPACE + TOTAL_INFRA + TOTAL_APPS + TOTAL_DOCS + TOTAL_CORE))

echo ""
echo -e "  ${BOLD}Blast Radius:${NC}"
echo "  ┌─────────────────────────────┬───────┐"
echo "  │ Zone                        │ Files │"
echo "  ├─────────────────────────────┼───────┤"
printf "  │ %-27s │ %5s │\n" "squads/$OLD_NAME/" "$TOTAL_SQUAD"
printf "  │ %-27s │ %5s │\n" ".claude/" "$TOTAL_CLAUDE"
printf "  │ %-27s │ %5s │\n" ".agents/skills/ (Codex)" "$TOTAL_CODEX"
printf "  │ %-27s │ %5s │\n" ".gemini/" "$TOTAL_GEMINI"
printf "  │ %-27s │ %5s │\n" ".agents/" "$TOTAL_AGENTS"
printf "  │ %-27s │ %5s │\n" ".cursor/rules/" "$TOTAL_CURSOR"
printf "  │ %-27s │ %5s │\n" "squads/ (cross-squad)" "$TOTAL_CROSSSQUAD"
printf "  │ %-27s │ %5s │\n" "workspace/" "$TOTAL_WORKSPACE"
printf "  │ %-27s │ %5s │\n" "infrastructure/" "$TOTAL_INFRA"
printf "  │ %-27s │ %5s │\n" "apps/" "$TOTAL_APPS"
printf "  │ %-27s │ %5s │\n" "docs/" "$TOTAL_DOCS"
printf "  │ %-27s │ %5s │\n" ".aiox-core/" "$TOTAL_CORE"
echo "  ├─────────────────────────────┼───────┤"
printf "  │ ${BOLD}%-27s${NC} │ ${BOLD}%5s${NC} │\n" "TOTAL" "$GRAND_TOTAL"
echo "  └─────────────────────────────┴───────┘"

if $DRY_RUN; then
  echo ""
  log_info "Dry-run complete. No changes made."
  echo -e "  Run without --dry-run to execute the rename."
  exit 0
fi

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 2: RENAME ESTRUTURAL
# ═══════════════════════════════════════════════════════════════════════════════
log_phase "PHASE 2: Rename Estrutural"

# Branch
if ! $NO_BRANCH; then
  git checkout -b "refactor/rename-${OLD_NAME}-to-${NEW_NAME}" 2>/dev/null || true
  log_pass "Branch: refactor/rename-${OLD_NAME}-to-${NEW_NAME}"
fi

# git mv
cd "$ROOT"
git mv "squads/$OLD_NAME" "squads/$NEW_NAME" 2>/dev/null || {
  # Fallback for untracked files
  mv "squads/$OLD_NAME" "squads/$NEW_NAME"
}
log_pass "Renamed squads/$OLD_NAME → squads/$NEW_NAME"

# Rename scripts inside squad
for f in "squads/$NEW_NAME/scripts/"*"$OLD_NAME"*; do
  [ -f "$f" ] || continue
  newf=$(echo "$f" | sed "s/$OLD_NAME/$NEW_NAME/g")
  mv "$f" "$newf" 2>/dev/null && log_pass "Script: $(basename "$f") → $(basename "$newf")"
done

# Also handle slug variants (e.g., "oldname" for "old-name")
OLD_SLUG=$(echo "$OLD_NAME" | tr -d '-')
if [[ "$OLD_SLUG" != "$OLD_NAME" ]]; then
  for f in "squads/$NEW_NAME/scripts/"*"$OLD_SLUG"*; do
    [ -f "$f" ] || continue
    NEW_SLUG=$(echo "$NEW_NAME" | tr -d '-')
    newf=$(echo "$f" | sed "s/$OLD_SLUG/$NEW_NAME/g")
    mv "$f" "$newf" 2>/dev/null && log_pass "Script: $(basename "$f") → $(basename "$newf")"
  done
fi

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 3: PROPAGAÇÃO (sed replace)
# ═══════════════════════════════════════════════════════════════════════════════
log_phase "PHASE 3: Propagação"

# Build sed expression
SED_ARGS=(
  -e "s|squads/$OLD_NAME/|squads/$NEW_NAME/|g"
  -e "s|squads/$OLD_NAME|squads/$NEW_NAME|g"
  -e "s|squad: $OLD_NAME|squad: $NEW_NAME|g"
  -e "s|name: $OLD_NAME|name: $NEW_NAME|g"
  -e "s|$OLD_NAME:agents:|$NEW_NAME:agents:|g"
  -e "s|$OLD_PASCAL:agents:|$NEW_PASCAL:agents:|g"
  -e "s|/$OLD_PASCAL:|/$NEW_PASCAL:|g"
  -e "s|domains/$OLD_NAME/|domains/$NEW_NAME/|g"
  -e "s|'$OLD_NAME'|'$NEW_NAME'|g"
  -e "s|\"$OLD_NAME\"|\"$NEW_NAME\"|g"
)

# Function to sed-replace in a directory
sed_replace() {
  local dir="$1"
  local label="$2"
  [ -d "$dir" ] || return 0
  local count
  count=$(find "$dir" -type f \( -name "*.md" -o -name "*.yaml" -o -name "*.yml" -o -name "*.cjs" -o -name "*.js" -o -name "*.ts" -o -name "*.tsx" -o -name "*.sh" -o -name "*.mdc" -o -name "*.json" \) 2>/dev/null | wc -l | tr -d ' ')
  if [[ "$count" -gt 0 ]]; then
    find "$dir" -type f \( -name "*.md" -o -name "*.yaml" -o -name "*.yml" -o -name "*.cjs" -o -name "*.js" -o -name "*.ts" -o -name "*.tsx" -o -name "*.sh" -o -name "*.mdc" -o -name "*.json" \) \
      -exec sed -i '' "${SED_ARGS[@]}" {} + 2>/dev/null
    log_pass "$label ($count files)"
  fi
}

# 3a: Squad internal
sed_replace "squads/$NEW_NAME" "Squad internal"

# 3b: Mirrors — rename dirs first, then sed content
for mirror_dir in \
  ".agents/skills/$OLD_PASCAL" \
  ".gemini/agents/$OLD_PASCAL" \
  ".agents/workflows/$OLD_PASCAL"; do
  if [ -d "$mirror_dir" ]; then
    new_mirror=$(echo "$mirror_dir" | sed "s|$OLD_PASCAL|$NEW_PASCAL|g")
    mv "$mirror_dir" "$new_mirror" 2>/dev/null && log_pass "Mirror dir: $(basename "$mirror_dir") → $(basename "$new_mirror")"
  fi
done

for mirror_dir in \
  ".claude/skills/$OLD_NAME" \
  ".agents/skills/$OLD_NAME"; do
  if [ -d "$mirror_dir" ]; then
    new_mirror=$(echo "$mirror_dir" | sed "s|$OLD_NAME|$NEW_NAME|g")
    mv "$mirror_dir" "$new_mirror" 2>/dev/null && log_pass "Mirror dir: $(basename "$mirror_dir") → $(basename "$new_mirror")"
  fi
done

# Rename agents/skills individual dirs (e.g., old-name-sub → new-name-sub)
for d in .agents/skills/${OLD_NAME}-*; do
  [ -d "$d" ] || continue
  newd=$(echo "$d" | sed "s|$OLD_NAME|$NEW_NAME|g")
  mv "$d" "$newd" 2>/dev/null && log_pass "Mirror dir: $(basename "$d") → $(basename "$newd")"
done

# 3c: Sed content in all mirrors
for dir in \
  ".claude/skills/$NEW_NAME" \
  ".claude/agents" \
  ".agents/skills/$NEW_PASCAL" \
  ".agents/skills/$NEW_NAME" \
  ".gemini/agents/$NEW_PASCAL" \
  ".agents/workflows/$NEW_PASCAL"; do
  sed_replace "$dir" "Mirror: $dir"
done

# 3d: Cross-squad refs
for squad_dir in "$SQUADS_DIR"/*/; do
  squad_name=$(basename "$squad_dir")
  [[ "$squad_name" == "$NEW_NAME" ]] && continue
  sed_replace "$squad_dir" "Cross-squad: $squad_name"
done

# 3e: Workspace domain rename
if [ -d "workspace/businesses/${OLD_NAME}" ]; then
  mv "workspace/businesses/${OLD_NAME}" "workspace/businesses/${NEW_NAME}" 2>/dev/null
  log_pass "Workspace domain renamed"
fi
if [ -f "workspace/config/mappings/${OLD_NAME}.clickup.yaml" ]; then
  mv "workspace/config/mappings/${OLD_NAME}.clickup.yaml" "workspace/config/mappings/${NEW_NAME}.clickup.yaml" 2>/dev/null
  log_pass "Workspace mapping renamed"
fi
sed_replace "workspace" "Workspace content"

# 3f: Cursor rules
sed_replace ".cursor/rules" "Cursor rules"

# 3g: Infrastructure
sed_replace "infrastructure" "Infrastructure"

# 3h: Apps
sed_replace "apps" "App code"

# 3i: .aiox-core
sed_replace ".aiox-core" ".aiox-core"

# 3j: AGENTS.md
if [ -f "AGENTS.md" ]; then
  sed -i '' "${SED_ARGS[@]}" "AGENTS.md" 2>/dev/null
  log_pass "AGENTS.md"
fi

# 3k: Docs (non-story)
find docs -type f -name "*.md" -not -name "*.story.md" -exec sed -i '' "${SED_ARGS[@]}" {} + 2>/dev/null
log_pass "Docs (non-story)"

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 4: VALIDAÇÃO
# ═══════════════════════════════════════════════════════════════════════════════
log_phase "PHASE 4: Validação"

# Grep residual
RESIDUAL_COUNT=$(grep -r "squads/$OLD_NAME" $EXTENSIONS -l "$ROOT" 2>/dev/null \
  | grep -v node_modules | grep -v ".git/" | grep -v ".story.md" \
  | grep -v ".aiox/worktrees/" | grep -v ".aiox/squad-runtime/" \
  | grep -v ".claude/worktrees/" \
  | grep -v "docs/projects/" | wc -l | tr -d ' ')

if [[ "$RESIDUAL_COUNT" -gt 0 ]]; then
  log_warn "Found $RESIDUAL_COUNT residual refs. Attempting auto-fix..."
  grep -r "squads/$OLD_NAME" $EXTENSIONS -l "$ROOT" 2>/dev/null \
    | grep -v node_modules | grep -v ".git/" | grep -v ".story.md" \
    | grep -v ".aiox/worktrees/" | grep -v ".aiox/squad-runtime/" \
    | grep -v ".claude/worktrees/" \
    | grep -v "docs/projects/" \
    | while read -r f; do
      sed -i '' "s|squads/$OLD_NAME|squads/$NEW_NAME|g" "$f" 2>/dev/null
    done

  # Re-check
  RESIDUAL_COUNT=$(grep -r "squads/$OLD_NAME" $EXTENSIONS -l "$ROOT" 2>/dev/null \
    | grep -v node_modules | grep -v ".git/" | grep -v ".story.md" \
    | grep -v ".aiox/worktrees/" | grep -v ".aiox/squad-runtime/" \
    | grep -v ".claude/worktrees/" \
    | grep -v "docs/projects/" | wc -l | tr -d ' ')
fi

if [[ "$RESIDUAL_COUNT" -eq 0 ]]; then
  log_pass "Zero residual refs to squads/$OLD_NAME"
else
  log_fail "$RESIDUAL_COUNT residual refs remain"
fi

# Check for hardcoded vars in validate-squad.sh
VALIDATE_SCRIPT="$SQUADS_DIR/squad-creator/scripts/validate-squad.sh"
if [ -f "$VALIDATE_SCRIPT" ]; then
  if grep -q "'$OLD_NAME'" "$VALIDATE_SCRIPT" 2>/dev/null || grep -q "\"$OLD_NAME\"" "$VALIDATE_SCRIPT" 2>/dev/null; then
    log_warn "validate-squad.sh has hardcoded '$OLD_NAME' reference. Fixing..."
    sed -i '' "s|'$OLD_NAME'|'$NEW_NAME'|g; s|\"$OLD_NAME\"|\"$NEW_NAME\"|g" "$VALIDATE_SCRIPT" 2>/dev/null
    # Also fix variable names like C_LEVEL_DIR
    OLD_VAR=$(echo "$OLD_NAME" | tr '[:lower:]-' '[:upper:]_')
    if grep -q "${OLD_VAR}" "$VALIDATE_SCRIPT" 2>/dev/null; then
      log_warn "Found ${OLD_VAR} variable in validate-squad.sh. Manual review recommended."
    fi
    log_pass "validate-squad.sh refs updated"
  fi
fi

# Run validate-squad
log_info "Running validate-squad $NEW_NAME --quick..."
if bash "$VALIDATE_SCRIPT" "$NEW_NAME" --quick 2>&1 | tail -5; then
  log_pass "validate-squad PASSED"
  VALIDATE_OK=true
else
  log_fail "validate-squad FAILED"
  VALIDATE_OK=false
fi

# ═══════════════════════════════════════════════════════════════════════════════
# SUMMARY
# ═══════════════════════════════════════════════════════════════════════════════
echo ""
echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${NC}"
if [[ "$RESIDUAL_COUNT" -eq 0 ]] && $VALIDATE_OK; then
  echo -e "${BOLD}║${GREEN}                    ✅ RENAME COMPLETE                        ${NC}${BOLD}║${NC}"
else
  echo -e "${BOLD}║${YELLOW}                   ⚠️  RENAME NEEDS REVIEW                    ${NC}${BOLD}║${NC}"
fi
echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "  Old: ${RED}$OLD_NAME${NC} → New: ${GREEN}$NEW_NAME${NC}"
echo -e "  Residual refs: $RESIDUAL_COUNT"
echo -e "  validate-squad: $(if $VALIDATE_OK; then echo "${GREEN}PASS${NC}"; else echo "${RED}FAIL${NC}"; fi)"
echo ""
echo -e "  ${BOLD}Next steps:${NC}"
echo -e "    1. Review changes: git diff --stat"
echo -e "    2. Commit: git add -A && git commit -m 'refactor(squads): rename $OLD_NAME to $NEW_NAME'"
echo -e "    3. Refresh registry: *refresh-registry"
echo ""

if [[ "$RESIDUAL_COUNT" -eq 0 ]] && $VALIDATE_OK; then
  exit 0
else
  exit 1
fi
