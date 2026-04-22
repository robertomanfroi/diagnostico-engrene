#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════════════════════════
# VALIDATE-SQUAD.SH - Hybrid Squad Validation Script
# ═══════════════════════════════════════════════════════════════════════════════
# Version: 4.0.0 - Dimensional Validation
# Compatibility: bash 3.2+ (macOS compatible)
# Purpose: Hybrid validation - bash for deterministic, Claude for qualitative
# Usage: ./validate-squad.sh <squad-name> [--verbose] [--quick] [--json]
#
# HYBRID APPROACH:
#   BASH (deterministic):
#     - File/directory existence
#     - Security scan (grep patterns)
#     - Cross-reference validation
#     - Metrics collection (counts, ratios)
#
#   CLAUDE CLI (qualitative):
#     - Prompt quality analysis
#     - Pipeline coherence evaluation
#     - Voice consistency check
#     - Overall assessment & recommendations
#
# Exit codes:
#   0 = PASS (score >= 7.0, no blocking issues)
#   1 = FAIL (score < 7.0 or blocking issues)
#   2 = ERROR (script error, invalid input)
# ═══════════════════════════════════════════════════════════════════════════════

set -uo pipefail

# Force C locale for numeric operations (awk/printf decimal separator)
export LC_NUMERIC=C

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SQUAD_CREATOR_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
SQUADS_DIR="$WORKSPACE_ROOT/squads"
RUNTIME_STATE_HELPER="$SCRIPT_DIR/lib/validate-runtime-state.cjs"
C_LEVEL_WORKSPACE_DIR="$SQUADS_DIR/c-level"
WORKFLOW_CONTRACT_VALIDATOR="$WORKSPACE_ROOT/infrastructure/scripts/squads/validate_workflow_contracts.cjs"
# ── Bootstrap all shared libs (runner-lib v2 + validator-lib) ──
RUNNER_LIB_DIR="$WORKSPACE_ROOT/infrastructure/scripts/runner-lib"
source "$RUNNER_LIB_DIR/pipeline-bootstrap.sh"
HAS_RUNTIME_LIB="${RUNNER_LIB_RUNTIME:-false}"
HAS_METRICS_LIB="${RUNNER_LIB_METRICS:-false}"

# Model configuration
MODEL_DEFAULT=""        # Resolved from runner-lib model catalog
MODEL_FAST=""           # Resolved from runner-lib model catalog
MODEL_QUALITY=""
MODEL_SELECTION_MODE="default"
SELECTED_RUNTIME="claude"  # Default runtime

refresh_runtime_models() {
  case "$SELECTED_RUNTIME" in
    claude)
      MODEL_DEFAULT="opus"
      MODEL_FAST="haiku"
      ;;
    codex)
      MODEL_DEFAULT="gpt-5.4"
      MODEL_FAST="gpt-5.4-mini"
      ;;
    gemini)
      MODEL_DEFAULT="gemini-3.1-pro-preview"
      MODEL_FAST="gemini-2.5-flash"
      ;;
  esac

  if declare -f get_quality_model >/dev/null 2>&1; then
    MODEL_DEFAULT="$(get_quality_model "$SELECTED_RUNTIME")"
    MODEL_FAST="$(get_fast_model "$SELECTED_RUNTIME")"
  fi
}

apply_runtime_selection() {
  local runtime="$1"
  SELECTED_RUNTIME="$runtime"
  refresh_runtime_models

  case "$MODEL_SELECTION_MODE" in
    fast)
      MODEL_QUALITY="$MODEL_FAST"
      ;;
    explicit)
      ;;
    *)
      MODEL_QUALITY="$MODEL_DEFAULT"
      ;;
  esac
}

apply_runtime_selection "$SELECTED_RUNTIME"
REQUESTED_RUNTIME="$SELECTED_RUNTIME"

# LLM runtime config (used by runtime.sh run_llm_prompt)
LLM_TIMEOUT_SECONDS="${SINKRA_LLM_TIMEOUT:-3600}"
RETRY_MAX_ATTEMPTS="${SINKRA_RETRY_MAX_ATTEMPTS:-2}"
RETRY_BASE_DELAY_SECONDS="${SINKRA_RETRY_BASE_DELAY:-3}"
export LLM_TIMEOUT_SECONDS RETRY_MAX_ATTEMPTS RETRY_BASE_DELAY_SECONDS SELECTED_RUNTIME

# Guards integrados em run_llm_prompt() (Story 101.12 AC8)
export COST_CAP_GUARD=true
export CIRCUIT_BREAKER_THRESHOLD=3
export HEADLESS_TRUNCATE_BYTES=12000
export HEADLESS_FILTER=true

# Replan-on-failure: validators use max 1 attempt (Story 101.10 AC9)
PHASE_REPLAN="${PHASE_REPLAN:-true}"
REPLAN_MAX_ATTEMPTS="${REPLAN_MAX_ATTEMPTS:-1}"
export PHASE_REPLAN REPLAN_MAX_ATTEMPTS
VALIDATION_SESSION_ID=""
VALIDATION_STATE_FILE=""

# Progress log path (set after SQUAD_NAME is known)
PROGRESS_LOG=""

# Append to progress log
_progress_log() {
  [[ -n "$PROGRESS_LOG" ]] && echo "$@" >> "$PROGRESS_LOG"
}

# Get historical scores from previous validation runs for LLM calibration
_get_historical_scores() {
  local history_dir="$WORKSPACE_ROOT/outputs/squad-validations/${SQUAD_NAME:-unknown}"
  if [[ ! -d "$history_dir" ]]; then
    echo "(no prior runs)"
    return
  fi
  local found=0
  for run_dir in "$history_dir"/2*; do
    [[ -d "$run_dir" && -f "$run_dir/score_card.yaml" ]] || continue
    local run_id
    run_id=$(basename "$run_dir")
    local prev_score
    prev_score=$(python3 -c "
import yaml
with open('$run_dir/score_card.yaml') as f:
    d = yaml.safe_load(f) or {}
s = d.get('scores',{})
print(f'{s.get(\"final\",\"?\")}/10 ({s.get(\"verdict\",\"?\")})')
" 2>/dev/null || echo "?")
    echo "- $run_id: $prev_score"
    found=$((found + 1))
    [[ "$found" -ge 5 ]] && break
  done
  [[ "$found" -eq 0 ]] && echo "(no prior runs)"
}

# _run_llm() removed — Story 101.12 AC8
# Guards (cost cap, circuit breaker, truncate, filter) now integrated in run_llm_prompt() via env vars.
# Call sites migrated to run_llm_prompt() direto.
# Note: _exec_runtime call at L4157 (evaluator) is intentionally left unchanged.

# Colors — provided by validator-lib/colors.sh if available, fallback inline
if [[ "${VALIDATOR_LIB_COLORS:-false}" != "true" ]]; then
  RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[0;33m'
  BLUE='\033[0;34m'; CYAN='\033[0;36m'; BOLD='\033[1m'; NC='\033[0m'
fi
MAGENTA='\033[0;36m'  # Using cyan — magenta/purple is unreadable on dark terminals

# Counters
PASS_COUNT=0
FAIL_COUNT=0
WARN_COUNT=0
DRY_RUN=false

# Results arrays
BLOCKING_ISSUES=""
WARNINGS=""

# Metrics (simple variables for bash 3.x compatibility)
M_AGENT_COUNT=0
M_TASK_COUNT=0
M_CHECKLIST_COUNT=0
M_TEMPLATE_COUNT=0
M_DATA_COUNT=0
M_TOTAL_LINES=0
M_SECURITY_ISSUES=0
M_XREF_ISSUES=0
M_OPG_WARNINGS=0
M_SQUAD_TYPE="unknown"
M_TYPE_CONFIDENCE=0
M_PROMPT_QUALITY=""
M_STRUCTURE_COHERENCE=""
M_COVERAGE_SCORE=""
M_DOCUMENTATION=""
M_QUALITY_SCORE="N/A"
M_IMPROVEMENTS=""
M_IMPROVEMENTS_REPORT=""
M_PROD_SCORE=0
M_WORKFLOW_CONTRACT_FILES=0
M_WORKFLOW_CONTRACT_ERRORS=0
M_WORKFLOW_CONTRACT_WARNINGS=0
CONFIG_TASK_IDS=""

# New dimensional metrics
M_AGNOSTICISM_VIOLATIONS=0
M_AGNOSTICISM_DETAILS=""
M_AGENT_QUALITY_GAPS=0
M_VERSION_CONSISTENT="true"
M_VERSION_DETAILS=""
M_STRUCT_COMPLETENESS_PASS=0
M_STRUCT_COMPLETENESS_TOTAL=0
M_CONTEXTUAL_LIFECYCLE_PASS=0
M_CONTEXTUAL_LIFECYCLE_TOTAL=0
M_CONTEXTUAL_LIFECYCLE_WARNINGS=0
M_HAS_TESTED_FLAG="false"
M_HAS_ARCHITECTURE_DOC="false"
M_HAS_UPDATE_TASK="false"
M_HAS_DELETE_TASK="false"

# Claude dimensional scores (populated by Phase 6)
CLAUDE_STRUCTURAL_COMPLETENESS=""
CLAUDE_SECURITY_AUDIT=""
CLAUDE_WORKFLOW_ANALYSIS=""
CLAUDE_AGENT_QUALITY=""
CLAUDE_SQUAD_AGNOSTICISM=""
CLAUDE_CONFIG_QUALITY=""
CLAUDE_PRODUCTION_EVIDENCE=""
CLAUDE_EXEC_SUMMARY=""
CLAUDE_EXEC_SUMMARY_REPORT=""
CLAUDE_BLOCKING_ANALYSIS=""
CLAUDE_RAW_JSON=""
CLAUDE_REPORT_JSON=""
SCORING_CAP_REASONS=""
FINAL_SCORE_RAW="0.00"
DIM_FUNCTIONALITY_NOTE=""
DIM_SECURITY_NOTE=""
DIM_WORKFLOW_CONTRACT_NOTE=""
DIM_STRUCTURAL_NOTE=""
DIM_AGENT_QUALITY_NOTE=""
DIM_AGNOSTICISM_NOTE=""
DIM_PRODUCTION_NOTE=""
DIM_CONFIG_NOTE=""
DIM_DOCUMENTATION_NOTE=""

# Phase results
TIER1_FAIL=0
SEC_FAIL=0
XREF_FAIL=0
WF_CONTRACT_FAIL=0
PROD_SCORE=0
PROD_MAX=5
FINAL_SCORE=0
ENTRY_AGENT=""
VALIDATION_RESULT="FAIL"
EXIT_CODE=1
CURRENT_PHASE="init"
REPORT_LANG="auto"
REPORT_LANG_RESOLVED="en"
REPORT_LANGUAGE_NAME="English"
ANALYSIS_LANG="en"
ANALYSIS_LANGUAGE_NAME="English"
LOCALIZED_REPORT_AVAILABLE="false"

normalize_lang_code() {
  local raw
  raw=$(printf '%s' "${1:-}" | tr '[:upper:]' '[:lower:]' | tr '_' '-')
  case "$raw" in
    ""|auto)
      echo "auto"
      ;;
    pt|pt-br|pt-pt|pt-*)
      echo "pt-br"
      ;;
    en|en-us|en-gb|en-*)
      echo "en"
      ;;
    *)
      echo "$raw"
      ;;
  esac
}

resolve_report_language() {
  local requested detected
  requested=$(normalize_lang_code "${REPORT_LANG:-auto}")
  detected="$requested"

  if [[ "$requested" == "auto" ]]; then
    detected=$(normalize_lang_code "${AIOX_VALIDATION_LANG:-${LANG:-${LC_MESSAGES:-${LC_ALL:-en}}}}")
  fi

  case "$detected" in
    pt-br)
      REPORT_LANG_RESOLVED="pt-br"
      REPORT_LANGUAGE_NAME="português brasileiro"
      ;;
    *)
      REPORT_LANG_RESOLVED="en"
      REPORT_LANGUAGE_NAME="English"
      ;;
  esac
}

t() {
  local key="$1"
  case "${REPORT_LANG_RESOLVED}:${key}" in
    pt-br:help_usage) echo "Uso: ./validate-squad.sh <squad-name> [opções]" ;;
    pt-br:help_arguments) echo "Argumentos:" ;;
    pt-br:help_arg_squad) echo "Nome do squad para validar (ex.: \"my-squad\", \"new-squad\")" ;;
    pt-br:help_options) echo "Opções:" ;;
    pt-br:help_verbose) echo "Mostra todos os checks e detalhes da análise profunda" ;;
    pt-br:help_quick) echo "Pula a análise do reviewer CLI (somente determinístico)" ;;
    pt-br:help_fast) echo "Usa Haiku em vez de Opus (mais barato e rápido)" ;;
    pt-br:help_json) echo "Emite resultados em JSON" ;;
    pt-br:help_lang) echo "Define idioma de saída: auto, pt-br, en" ;;
    pt-br:help_help) echo "Mostra esta ajuda" ;;
    pt-br:help_examples) echo "Exemplos:" ;;
    pt-br:help_example_full) echo "Validação completa com Opus" ;;
    pt-br:help_example_verbose) echo "Saída verbosa" ;;
    pt-br:help_example_quick) echo "Somente determinístico (sem reviewer CLI)" ;;
    pt-br:help_example_fast) echo "Validação rápida com Haiku" ;;
    pt-br:help_example_lang) echo "Força relatório em português" ;;
    pt-br:help_exit_codes) echo "Códigos de saída:" ;;
    pt-br:help_exit_pass) echo "PASS     Nota >= 7.0, sem issues bloqueantes" ;;
    pt-br:help_exit_fail) echo "FAIL     Nota < 7.0 ou com issues bloqueantes" ;;
    pt-br:help_exit_error) echo "ERROR    Input inválido ou erro do script" ;;
    pt-br:unknown_option) echo "Opção desconhecida: %s" ;;
    pt-br:error_squad_required) echo "Erro: nome do squad é obrigatório" ;;
    pt-br:error_usage_simple) echo "Uso: ./validate-squad.sh <squad-name>" ;;
    pt-br:error_squad_not_found) echo "Erro: squad não encontrado: %s" ;;
    pt-br:main_title) echo "🔍 VALIDATE-SQUAD v4.0 - Validação Dimensional" ;;
    pt-br:label_squad) echo "Squad" ;;
    pt-br:label_path) echo "Caminho" ;;
    pt-br:label_mode) echo "Modo" ;;
    pt-br:label_model) echo "Modelo" ;;
    pt-br:mode_quick) echo "rápido (sem reviewer CLI)" ;;
    pt-br:mode_hybrid) echo "híbrido" ;;
    pt-br:phase6_title) echo "PHASE 6: Análise Profunda de Qualidade (Claude CLI)" ;;
    pt-br:phase6_skip) echo "Pulando análise do reviewer CLI (--quick mode)" ;;
    pt-br:phase6_running) echo "Executando análise profunda com Claude usando %s..." ;;
    pt-br:phase6_prompt_written) echo "Prompt gravado em arquivo temporário (%s bytes)" ;;
    pt-br:phase6_result) echo "Resultado da Análise Profunda do Claude:" ;;
    pt-br:phase6_failed) echo "Análise do reviewer CLI falhou; usando score determinístico" ;;
    pt-br:phase6_complete) echo "Análise profunda do reviewer concluída" ;;
    pt-br:phase6_language_state) echo "Artefato canônico: %s | Relatório: %s" ;;
    pt-br:phase6_localization_fallback) echo "Localização do reviewer indisponível; exibindo artefato canônico em inglês" ;;
    pt-br:phase7_title) echo "PHASE 7: Pontuação Final (Dimensional)" ;;
    pt-br:scoring_breakdown) echo "Composição da pontuação:" ;;
    pt-br:weighted_avg) echo "Média ponderada (pré-penalidade): %s" ;;
    pt-br:penalty) echo "Penalidade: -%s" ;;
    pt-br:after_penalty) echo "Após penalidade: %s" ;;
    pt-br:after_caps) echo "Após caps: %s" ;;
    pt-br:cap_reasons) echo "Motivos do cap: %s" ;;
    pt-br:final_rounded) echo "Final (arredondado): %s/10" ;;
    pt-br:validation_passed) echo "VALIDAÇÃO APROVADA" ;;
    pt-br:validation_conditional) echo "APROVAÇÃO CONDICIONAL" ;;
    pt-br:validation_failed) echo "VALIDAÇÃO REPROVADA" ;;
    pt-br:verdict_pass) echo "APROVADO" ;;
    pt-br:verdict_conditional) echo "CONDICIONAL" ;;
    pt-br:verdict_fail) echo "REPROVADO" ;;
    pt-br:label_type) echo "Tipo" ;;
    pt-br:label_final) echo "Final" ;;
    pt-br:label_raw) echo "Bruto" ;;
    pt-br:label_verdict) echo "Veredicto" ;;
    pt-br:label_analysis_language) echo "Idioma da Análise" ;;
    pt-br:label_report_language) echo "Idioma do Relatório" ;;
    pt-br:dimensional_scores) echo "Pontuação por Dimensão" ;;
    pt-br:table_dimension) echo "Dimensão" ;;
    pt-br:table_score) echo "Nota" ;;
    pt-br:table_weight) echo "Peso" ;;
    pt-br:weight_high) echo "ALTO" ;;
    pt-br:weight_medium) echo "MÉDIO" ;;
    pt-br:weight_low) echo "BAIXO" ;;
    pt-br:dimension_notes) echo "Notas por Dimensão (<10)" ;;
    pt-br:blocking_issues) echo "Issues Bloqueantes" ;;
    pt-br:score_guardrails) echo "Guardrails de Pontuação" ;;
    pt-br:deterministic_findings) echo "Achados Determinísticos" ;;
    pt-br:table_check) echo "Check" ;;
    pt-br:table_count) echo "Contagem" ;;
    pt-br:version_consistency) echo "Consistência de Versão" ;;
    pt-br:version_mismatch) echo "DIVERGÊNCIA" ;;
    pt-br:priority_fixes) echo "Correções Prioritárias" ;;
    pt-br:improvements) echo "Melhorias" ;;
    pt-br:production_none) echo "Sem evidência de uso real — nota máxima limitada a 5/10" ;;
    pt-br:production_limited) echo "Evidência de produção limitada — nota máxima limitada a 7/10" ;;
    pt-br:production_good) echo "Boa evidência de produção" ;;
    pt-br:functionality_label) echo "Funcionalidade/Pipeline" ;;
    pt-br:security_label) echo "Segurança" ;;
    pt-br:agnosticism_label) echo "Agnosticismo do Squad" ;;
    pt-br:production_label) echo "Evidência de Produção" ;;
    pt-br:workflow_contract_label) echo "Contrato de Workflow" ;;
    pt-br:structural_label) echo "Completude Estrutural" ;;
    pt-br:agent_quality_label) echo "Qualidade do Agente" ;;
    pt-br:config_quality_label) echo "Qualidade da Configuração" ;;
    pt-br:documentation_label) echo "Documentação" ;;
    pt-br:check_tier1) echo "Falhas TIER1" ;;
    pt-br:check_security) echo "Issues de Segurança" ;;
    pt-br:check_xref) echo "Referências Quebradas" ;;
    pt-br:check_workflow_contract) echo "Erros de Contrato de Workflow" ;;
    pt-br:check_agnosticism) echo "Violações de Agnosticismo" ;;
    pt-br:check_agent_quality) echo "Gaps de Qualidade do Agente" ;;
    pt-br:check_structural) echo "Estrutural Obrigatório" ;;
    pt-br:check_contextual_lifecycle) echo "Lifecycle Contextual" ;;
    pt-br:check_warnings) echo "Warnings" ;;
    pt-br:note_functionality_deep) echo "deep review retornou workflow_analysis=%s/10" ;;
    pt-br:note_functionality_quick_max) echo "fallback do quick mode limita Funcionalidade a 9/10 sem análise profunda" ;;
    pt-br:note_functionality_quick_reduced) echo "fallback do quick mode reduziu Funcionalidade por %s" ;;
    pt-br:note_security_deep) echo "deep review retornou security_audit=%s/10" ;;
    pt-br:note_security_deterministic) echo "fallback determinístico de Segurança baseado em security_fail=%s" ;;
    pt-br:note_workflow_neutral) echo "sem diretório de workflows; contrato de workflow ficou neutro em 5/10" ;;
    pt-br:note_workflow_deterministic) echo "nota do contrato de workflow refletiu errors=%s, warnings=%s" ;;
    pt-br:note_structural_deep) echo "deep review retornou structural_completeness=%s/10" ;;
    pt-br:note_structural_deterministic) echo "nota estrutural determinística baseada em checks obrigatórios=%s/%s e tier1_fail=%s" ;;
    pt-br:note_agent_deep) echo "deep review retornou agent_quality=%s/10" ;;
    pt-br:note_agent_deterministic) echo "entry agent sem %s de 5 seções estruturais" ;;
    pt-br:note_agnosticism_deep) echo "deep review retornou squad_agnosticism=%s/10" ;;
    pt-br:note_agnosticism_deterministic) echo "nota determinística de agnosticismo baseada em violations=%s" ;;
    pt-br:note_production_deep) echo "deep review retornou production_evidence=%s/10" ;;
    pt-br:note_production_deterministic) echo "nota determinística de produção baseada em evidência=%s/%s" ;;
    pt-br:note_config_deep) echo "deep review retornou config_quality=%s/10" ;;
    pt-br:note_config_missing) echo "rubrica determinística de configuração com lacunas: %s (%s/%s sinais)" ;;
    pt-br:note_config_generic) echo "rubrica determinística de configuração não atingiu 10/10" ;;
    pt-br:note_documentation_deep) echo "deep review retornou documentation=%s/10" ;;
    pt-br:note_documentation_deterministic) echo "nota determinística de documentação com lacunas: %s" ;;
    pt-br:guardrail_prod_5) echo "cap de produção: score <= 5 sem evidência de produção" ;;
    pt-br:guardrail_prod_7) echo "cap de produção: score <= 7 com evidência limitada" ;;
    pt-br:guardrail_prod_9) echo "cap de produção: score <= 9 sem evidência completa" ;;
    pt-br:guardrail_blocking) echo "issues bloqueantes abertos impõem score <= 6" ;;
    pt-br:guardrail_combined) echo "dívida combinada em dimensões críticas impõe score <= 5" ;;
    pt-br:guardrail_high) echo "dívida grave em dimensão HIGH impõe score <= 6" ;;
    pt-br:guardrail_medium) echo "múltiplas dívidas graves em dimensões MEDIUM impõem score <= 6" ;;
    pt-br:guardrail_critical_dimension) echo "dimensão crítica %s=%s" ;;
    en:help_usage) echo "Usage: ./validate-squad.sh <squad-name> [options]" ;;
    en:help_arguments) echo "Arguments:" ;;
    en:help_arg_squad) echo "Name of squad to validate (e.g., \"my-squad\", \"new-squad\")" ;;
    en:help_options) echo "Options:" ;;
    en:help_verbose) echo "Show all checks and deep analysis details" ;;
    en:help_quick) echo "Skip reviewer CLI analysis (deterministic only)" ;;
    en:help_fast) echo "Use Haiku instead of Opus (cheaper, faster)" ;;
    en:help_json) echo "Output results as JSON" ;;
    en:help_lang) echo "Set output language: auto, pt-br, en" ;;
    en:help_help) echo "Show this help message" ;;
    en:help_examples) echo "Examples:" ;;
    en:help_example_full) echo "Full validation with Opus" ;;
    en:help_example_verbose) echo "Verbose output" ;;
    en:help_example_quick) echo "Deterministic only (no reviewer CLI)" ;;
    en:help_example_fast) echo "Quick validation with Haiku" ;;
    en:help_example_lang) echo "Force English report" ;;
    en:help_exit_codes) echo "Exit Codes:" ;;
    en:help_exit_pass) echo "PASS     Score >= 7.0, no blocking issues" ;;
    en:help_exit_fail) echo "FAIL     Score < 7.0 or blocking issues found" ;;
    en:help_exit_error) echo "ERROR    Invalid input or script error" ;;
    en:unknown_option) echo "Unknown option: %s" ;;
    en:error_squad_required) echo "Error: Squad name required" ;;
    en:error_usage_simple) echo "Usage: ./validate-squad.sh <squad-name>" ;;
    en:error_squad_not_found) echo "Error: Squad not found: %s" ;;
    en:main_title) echo "🔍 VALIDATE-SQUAD v4.0 - Dimensional Validation" ;;
    en:label_squad) echo "Squad" ;;
    en:label_path) echo "Path" ;;
    en:label_mode) echo "Mode" ;;
    en:label_model) echo "Model" ;;
    en:mode_quick) echo "quick (no reviewer CLI)" ;;
    en:mode_hybrid) echo "hybrid" ;;
    en:phase6_title) echo "PHASE 6: Deep Quality Analysis (Claude CLI)" ;;
    en:phase6_skip) echo "Skipping reviewer CLI analysis (--quick mode)" ;;
    en:phase6_running) echo "Running Claude deep analysis with %s..." ;;
    en:phase6_prompt_written) echo "Prompt written to temp file (%s bytes)" ;;
    en:phase6_result) echo "Claude Deep Analysis Result:" ;;
    en:phase6_failed) echo "Reviewer CLI analysis failed; using deterministic score only" ;;
    en:phase6_complete) echo "Reviewer CLI deep analysis complete" ;;
    en:phase6_language_state) echo "Canonical artifact: %s | Report: %s" ;;
    en:phase6_localization_fallback) echo "Reviewer localization unavailable; showing canonical English artifact" ;;
    en:phase7_title) echo "PHASE 7: Final Scoring (Dimensional)" ;;
    en:scoring_breakdown) echo "Scoring breakdown:" ;;
    en:weighted_avg) echo "Weighted avg (pre-penalty): %s" ;;
    en:penalty) echo "Penalty: -%s" ;;
    en:after_penalty) echo "After penalty: %s" ;;
    en:after_caps) echo "After caps: %s" ;;
    en:cap_reasons) echo "Cap reasons: %s" ;;
    en:final_rounded) echo "Final (rounded): %s/10" ;;
    en:validation_passed) echo "VALIDATION PASSED" ;;
    en:validation_conditional) echo "CONDITIONAL PASS" ;;
    en:validation_failed) echo "VALIDATION FAILED" ;;
    en:verdict_pass) echo "PASS" ;;
    en:verdict_conditional) echo "CONDITIONAL" ;;
    en:verdict_fail) echo "FAIL" ;;
    en:label_type) echo "Type" ;;
    en:label_final) echo "Final" ;;
    en:label_raw) echo "Raw" ;;
    en:label_verdict) echo "Verdict" ;;
    en:label_analysis_language) echo "Analysis Language" ;;
    en:label_report_language) echo "Report Language" ;;
    en:dimensional_scores) echo "Dimensional Scores" ;;
    en:table_dimension) echo "Dimension" ;;
    en:table_score) echo "Score" ;;
    en:table_weight) echo "Weight" ;;
    en:weight_high) echo "HIGH" ;;
    en:weight_medium) echo "MEDIUM" ;;
    en:weight_low) echo "LOW" ;;
    en:dimension_notes) echo "Dimension Notes (<10)" ;;
    en:blocking_issues) echo "Blocking Issues" ;;
    en:score_guardrails) echo "Score Guardrails" ;;
    en:deterministic_findings) echo "Deterministic Findings" ;;
    en:table_check) echo "Check" ;;
    en:table_count) echo "Count" ;;
    en:version_consistency) echo "Version Consistency" ;;
    en:version_mismatch) echo "MISMATCH" ;;
    en:priority_fixes) echo "Priority Fixes" ;;
    en:improvements) echo "Improvements" ;;
    en:production_none) echo "No evidence of real usage — max possible score capped at 5/10" ;;
    en:production_limited) echo "Limited production evidence — max possible score capped at 7/10" ;;
    en:production_good) echo "Good production evidence" ;;
    en:functionality_label) echo "Functionality/Pipeline" ;;
    en:security_label) echo "Security" ;;
    en:agnosticism_label) echo "Squad Agnosticism" ;;
    en:production_label) echo "Production Evidence" ;;
    en:workflow_contract_label) echo "Workflow Contract" ;;
    en:structural_label) echo "Structural Completeness" ;;
    en:agent_quality_label) echo "Agent Quality" ;;
    en:config_quality_label) echo "Config Quality" ;;
    en:documentation_label) echo "Documentation" ;;
    en:check_tier1) echo "TIER1 Failures" ;;
    en:check_security) echo "Security Issues" ;;
    en:check_xref) echo "Cross-Ref Broken" ;;
    en:check_workflow_contract) echo "Workflow Contract Errors" ;;
    en:check_agnosticism) echo "Agnosticism Violations" ;;
    en:check_agent_quality) echo "Agent Quality Gaps" ;;
    en:check_structural) echo "Mandatory Structural" ;;
    en:check_contextual_lifecycle) echo "Contextual Lifecycle" ;;
    en:check_warnings) echo "Warnings" ;;
    en:note_functionality_deep) echo "deep review returned workflow_analysis=%s/10" ;;
    en:note_functionality_quick_max) echo "quick-mode fallback maxes at 9/10 without deep review" ;;
    en:note_functionality_quick_reduced) echo "quick-mode fallback reduced by %s" ;;
    en:note_security_deep) echo "deep review returned security_audit=%s/10" ;;
    en:note_security_deterministic) echo "deterministic security fallback based on security_fail=%s" ;;
    en:note_workflow_neutral) echo "no workflows directory detected; workflow contract kept neutral at 5/10" ;;
    en:note_workflow_deterministic) echo "workflow contract score reflects errors=%s, warnings=%s" ;;
    en:note_structural_deep) echo "deep review returned structural_completeness=%s/10" ;;
    en:note_structural_deterministic) echo "deterministic structural score from mandatory checks=%s/%s and tier1_fail=%s" ;;
    en:note_agent_deep) echo "deep review returned agent_quality=%s/10" ;;
    en:note_agent_deterministic) echo "entry agent missing %s of 5 structural sections" ;;
    en:note_agnosticism_deep) echo "deep review returned squad_agnosticism=%s/10" ;;
    en:note_agnosticism_deterministic) echo "deterministic agnosticism score based on violations=%s" ;;
    en:note_production_deep) echo "deep review returned production_evidence=%s/10" ;;
    en:note_production_deterministic) echo "deterministic production score based on production evidence=%s/%s" ;;
    en:note_config_deep) echo "deep review returned config_quality=%s/10" ;;
    en:note_config_missing) echo "deterministic config rubric missing or weak: %s (%s/%s signals)" ;;
    en:note_config_generic) echo "deterministic config rubric did not reach 10/10" ;;
    en:note_documentation_deep) echo "deep review returned documentation=%s/10" ;;
    en:note_documentation_deterministic) echo "deterministic documentation score missing or weak: %s" ;;
    en:guardrail_prod_5) echo "production cap: score <= 5 without production evidence" ;;
    en:guardrail_prod_7) echo "production cap: score <= 7 with limited evidence" ;;
    en:guardrail_prod_9) echo "production cap: score <= 9 without full evidence" ;;
    en:guardrail_blocking) echo "open blocking issues force score <= 6" ;;
    en:guardrail_combined) echo "combined critical dimension debt forces score <= 5" ;;
    en:guardrail_high) echo "critical HIGH dimension debt forces score <= 6" ;;
    en:guardrail_medium) echo "multiple critical MEDIUM dimension debts force score <= 6" ;;
    en:guardrail_critical_dimension) echo "critical dimension %s=%s" ;;
    *)
      echo "$key"
      ;;
  esac
}

fmt_t() {
  local key="$1"
  shift
  local format
  format=$(t "$key")
  printf "$format" "$@"
}

dimension_label() {
  case "$1" in
    functionality) t "functionality_label" ;;
    security) t "security_label" ;;
    squad_agnosticism) t "agnosticism_label" ;;
    production_evidence) t "production_label" ;;
    workflow_contract) t "workflow_contract_label" ;;
    structural_completeness) t "structural_label" ;;
    agent_quality) t "agent_quality_label" ;;
    config_quality) t "config_quality_label" ;;
    documentation) t "documentation_label" ;;
    *) printf '%s' "$1" ;;
  esac
}

weight_label() {
  case "$1" in
    HIGH) t "weight_high" ;;
    MEDIUM) t "weight_medium" ;;
    LOW) t "weight_low" ;;
    *) printf '%s' "$1" ;;
  esac
}

deterministic_check_label() {
  case "$1" in
    tier1) t "check_tier1" ;;
    security) t "check_security" ;;
    xref) t "check_xref" ;;
    workflow_contract) t "check_workflow_contract" ;;
    agnosticism) t "check_agnosticism" ;;
    agent_quality) t "check_agent_quality" ;;
    structural) t "check_structural" ;;
    contextual_lifecycle) t "check_contextual_lifecycle" ;;
    warnings) t "check_warnings" ;;
    *) printf '%s' "$1" ;;
  esac
}

translate_guardrail_reason() {
  local reason="$1"
  case "$reason" in
    "production_cap:score<=5_without_production") t "guardrail_prod_5" ;;
    "production_cap:score<=7_with_limited_evidence") t "guardrail_prod_7" ;;
    "production_cap:score<=9_without_full_evidence") t "guardrail_prod_9" ;;
    "blocking_issues_open:score<=6") t "guardrail_blocking" ;;
    "combined_critical_dimension_debt:score<=5") t "guardrail_combined" ;;
    "critical_high_dimension_debt:score<=6") t "guardrail_high" ;;
    "multiple_medium_dimension_debt:score<=6") t "guardrail_medium" ;;
    critical_dimension:*=*)
      local name="${reason#critical_dimension:}"
      local value="${name#*=}"
      name="${name%%=*}"
      fmt_t "guardrail_critical_dimension" "$(dimension_label "$name")" "$value"
      ;;
    *)
      printf '%s' "$reason"
      ;;
  esac
}

# ═══════════════════════════════════════════════════════════════════════════════
# ARGUMENT PARSING
# ═══════════════════════════════════════════════════════════════════════════════

show_help() {
  resolve_report_language
  echo "╔══════════════════════════════════════════════════════════════╗"
  printf "║ %-60s ║\n" "$(t main_title)"
  echo "╚══════════════════════════════════════════════════════════════╝"
  echo ""
  echo "$(t help_usage)"
  echo ""
  echo "$(t help_arguments)"
  printf "  squad-name    %s\n" "$(t help_arg_squad)"
  echo ""
  echo "$(t help_options)"
  printf "  --verbose     %s\n" "$(t help_verbose)"
  printf "  --quick       %s\n" "$(t help_quick)"
  printf "  --fast        %s\n" "$(t help_fast)"
  printf "  --json        %s\n" "$(t help_json)"
  printf "  --lang        %s\n" "$(t help_lang)"
  printf "  --help        %s\n" "$(t help_help)"
  echo ""
  echo "$(t help_examples)"
  printf "  ./validate-squad.sh {squad-name}                # %s\n" "$(t help_example_full)"
  printf "  ./validate-squad.sh {squad-name} --verbose      # %s\n" "$(t help_example_verbose)"
  printf "  ./validate-squad.sh {squad-name} --quick        # %s\n" "$(t help_example_quick)"
  printf "  ./validate-squad.sh {squad-name} --fast         # %s\n" "$(t help_example_fast)"
  printf "  ./validate-squad.sh {squad-name} --lang pt-br   # %s\n" "$(t help_example_lang)"
  echo ""
  echo "$(t help_exit_codes)"
  printf "  0  %s\n" "$(t help_exit_pass)"
  printf "  1  %s\n" "$(t help_exit_fail)"
  printf "  2  %s\n" "$(t help_exit_error)"
  exit 0
}

SQUAD_NAME=""
VERBOSE=false
QUICK_MODE=false
JSON_OUTPUT=false
FAST_MODE=false

handle_extra_args() {
  POSITIONAL_ARGS=()
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --fast|-f)
        FAST_MODE=true
        MODEL_SELECTION_MODE="fast"
        shift
        ;;
      --lang)
        if [[ $# -lt 2 ]]; then
          resolve_report_language
          echo "$(t error_usage_simple)"
          exit 2
        fi
        REPORT_LANG="$2"
        shift 2
        ;;
      -*)
        resolve_report_language
        fmt_t "unknown_option" "$1"
        echo ""
        exit 2
        ;;
      *)
        POSITIONAL_ARGS+=("$1")
        shift
        ;;
    esac
  done
}

parse_common_args "$@"
parse_extra_flags "${POSITIONAL_ARGS[@]}"

QUICK_MODE="$QUICK"
if [[ -n "${REQUESTED_RUNTIME:-}" ]]; then
  apply_runtime_selection "$REQUESTED_RUNTIME"
fi
if [[ "$FAST_MODE" == "true" ]]; then
  MODEL_QUALITY="$MODEL_FAST"
fi
if [[ -n "${RUNNER_MODEL:-}" ]]; then
  MODEL_QUALITY="$RUNNER_MODEL"
  MODEL_SELECTION_MODE="explicit"
fi
if [[ ${#POSITIONAL_ARGS[@]} -gt 1 ]]; then
  resolve_report_language
  fmt_t "unknown_option" "${POSITIONAL_ARGS[1]}"
  echo ""
  exit 2
fi
SQUAD_NAME="${POSITIONAL_ARGS[0]:-}"

# Validate and export runtime for libs
export SELECTED_RUNTIME
if [[ "$HAS_RUNTIME_LIB" == "true" ]]; then
  validate_runtime "$SELECTED_RUNTIME"
fi

REPORT_LANG=$(normalize_lang_code "${REPORT_LANG:-auto}")
resolve_report_language

case "$REPORT_LANG" in
  auto|"")
    ;;
  pt|pt-br|en)
    ;;
  *)
    fmt_t "unknown_option" "--lang $REPORT_LANG"
    echo ""
    exit 2
    ;;
esac

if [[ -z "$SQUAD_NAME" ]]; then
  echo "$(t error_squad_required)"
  echo "$(t error_usage_simple)"
  exit 2
fi

SQUAD_DIR="$SQUADS_DIR/$SQUAD_NAME"

# Initialize progress log and metrics
PROGRESS_LOG="$WORKSPACE_ROOT/outputs/squad-validations/$SQUAD_NAME/progress.txt"
METRICS_FILE="$WORKSPACE_ROOT/outputs/squad-validations/$SQUAD_NAME/metrics.jsonl"
MAX_COST="${SINKRA_MAX_COST:-5.00}"
export METRICS_FILE MAX_COST
mkdir -p "$(dirname "$PROGRESS_LOG")"
VALIDATION_STATE_FILE="$WORKSPACE_ROOT/outputs/squad-validations/$SQUAD_NAME/validation-state.json"
if declare -f state_init >/dev/null 2>&1; then
  state_init "$VALIDATION_STATE_FILE" "$SQUAD_NAME" "squad-validation" "{\"runtime\":\"$SELECTED_RUNTIME\"}" || true
  state_phase_update "$VALIDATION_STATE_FILE" "validation" "running" "validate-squad" || true
fi
if declare -f session_start >/dev/null 2>&1; then
  VALIDATION_SESSION_ID="$(session_start "squad-creator" "validate-squad" "$SQUAD_NAME" "$MODEL_QUALITY" "$SELECTED_RUNTIME" "$PROGRESS_LOG" "{\"type\":\"squad-validation\"}" 2>/dev/null || true)"
fi

validate_squad_cleanup() {
  local exit_code=$?
  if declare -f state_phase_update >/dev/null 2>&1 && [[ -n "$VALIDATION_STATE_FILE" ]]; then
    state_phase_update "$VALIDATION_STATE_FILE" "validation" "$([[ "$exit_code" -eq 0 ]] && echo complete || echo failed)" "validate-squad" >/dev/null 2>&1 || true
  fi
  if declare -f session_end >/dev/null 2>&1 && [[ -n "$VALIDATION_SESSION_ID" ]]; then
    session_end "$VALIDATION_SESSION_ID" "$exit_code" >/dev/null 2>&1 || true
  fi
}
trap validate_squad_cleanup EXIT

{
  echo ""
  echo "--- Validation session: $(date -Iseconds) ---"
  echo "Squad: $SQUAD_NAME | Runtime: $SELECTED_RUNTIME | Model: $MODEL_QUALITY"
} >> "$PROGRESS_LOG"

if [[ ! -d "$SQUAD_DIR" ]]; then
  fmt_t "error_squad_not_found" "$SQUAD_DIR"
  echo ""
  exit 2
fi

INHERITED_SQUAD=""
INHERITED_SQUAD_DIR=""
if [[ -f "$SQUAD_DIR/config.yaml" ]]; then
  INHERITED_SQUAD=$(grep -E '^[[:space:]]*enhances:[[:space:]]*' "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/.*enhances:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs || true)
  if [[ -z "$INHERITED_SQUAD" ]]; then
    INHERITED_SQUAD=$(grep -E '^[[:space:]]*enhances:[[:space:]]*' "$SQUAD_DIR/config.yaml" 2>/dev/null | tail -1 | sed 's/.*enhances:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs || true)
  fi
  if [[ -n "$INHERITED_SQUAD" ]] && [[ -d "$SQUADS_DIR/$INHERITED_SQUAD" ]]; then
    INHERITED_SQUAD_DIR="$SQUADS_DIR/$INHERITED_SQUAD"
  fi
fi

# ═══════════════════════════════════════════════════════════════════════════════
# LOGGING HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

log_pass() {
  PASS_COUNT=$((PASS_COUNT + 1))
  if [[ "$VERBOSE" == "true" ]]; then
    echo -e "  ${GREEN}✓${NC} $1"
  fi
}

log_fail() {
  FAIL_COUNT=$((FAIL_COUNT + 1))
  echo -e "  ${RED}✗${NC} $1"
  BLOCKING_ISSUES="${BLOCKING_ISSUES}${1}"$'\n'
}

log_warn() {
  WARN_COUNT=$((WARN_COUNT + 1))
  echo -e "  ${YELLOW}⚠${NC} $1"
  WARNINGS="${WARNINGS}${1}"$'\n'
}

log_info() {
  if [[ "$VERBOSE" == "true" ]]; then
    echo -e "  ${CYAN}ℹ${NC} $1"
  fi
}

asset_exists() {
  local asset_type="$1"
  local asset_name="$2"

  if [[ -f "$SQUAD_DIR/$asset_type/$asset_name" ]]; then
    return 0
  fi

  if [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/$asset_type/$asset_name" ]]; then
    return 0
  fi

  return 1
}

log_section() {
  echo ""
  echo -e "${BOLD}${BLUE}═══ $1 ═══${NC}"
}

log_subsection() {
  echo -e "${CYAN}--- $1 ---${NC}"
}

# Runtime state helper (best-effort, non-blocking)
runtime_state_call() {
  if [[ ! -f "$RUNTIME_STATE_HELPER" ]]; then
    return 0
  fi

  if ! node "$RUNTIME_STATE_HELPER" "$@" >/dev/null 2>&1; then
    echo -e "${YELLOW}⚠ Runtime state update failed (${*})${NC}" >&2
    return 1
  fi

  return 0
}

runtime_state_start() {
  local mode="hybrid"
  if [[ "$QUICK_MODE" == "true" ]]; then
    mode="quick"
  fi

  runtime_state_call start \
    --squad "$SQUAD_NAME" \
    --mode "$mode" \
    --model "$MODEL_QUALITY" \
    --quick "$QUICK_MODE" \
    --verbose "$VERBOSE" \
    --json "$JSON_OUTPUT"
}

runtime_state_phase_start() {
  local phase="$1"
  CURRENT_PHASE="$phase"
  runtime_state_call phase --squad "$SQUAD_NAME" --phase "$phase" --status in_progress
}

runtime_state_phase_complete() {
  local phase="$1"
  local status="${2:-completed}"
  runtime_state_call phase --squad "$SQUAD_NAME" --phase "$phase" --status "$status"
}

runtime_state_complete() {
  local status="$1"
  runtime_state_call complete \
    --squad "$SQUAD_NAME" \
    --status "$status" \
    --result "$VALIDATION_RESULT" \
    --final-score "$FINAL_SCORE" \
    --exit-code "$EXIT_CODE" \
    --warnings "$WARN_COUNT" \
    --tier1-fail "$TIER1_FAIL" \
    --security-fail "$SEC_FAIL" \
    --workflow-contract-fail "$WF_CONTRACT_FAIL" \
    --xref-fail "$XREF_FAIL" \
    --phase "$CURRENT_PHASE"
}

# ═══════════════════════════════════════════════════════════════════════════════
# SCORING/JSON HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

is_numeric_score() {
  [[ "$1" =~ ^[0-9]+([.][0-9]+)?$ ]]
}

clamp_score_0_10() {
  awk -v n="$1" 'BEGIN { if (n < 0) n = 0; if (n > 10) n = 10; printf "%.2f", n }'
}

round_score_0_10_int() {
  awk -v n="$1" 'BEGIN { if (n < 0) n = 0; if (n > 10) n = 10; printf "%d", int(n + 0.5) }'
}

extract_first_json_object() {
  # Read piped data into variable, then pass via env var to avoid
  # stdin conflict with heredoc (heredoc consumes stdin, breaking pipe input).
  local input
  input=$(cat)
  if [[ "${RUNNER_LIB_JSON_VALIDATOR:-false}" == "true" ]]; then
    local extracted=""
    extracted=$(json_extract "$input" 2>/dev/null || true)
    if [[ -n "$extracted" ]] && json_validate "$extracted"; then
      printf '%s' "$extracted"
      return 0
    fi
  fi
  __JSON_EXTRACT_INPUT="$input" python3 <<'PY'
import json
import os
import re

text = os.environ.get('__JSON_EXTRACT_INPUT', '')
text = re.sub(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])', '', text)
text = text.replace("```json", "```").replace("```JSON", "```")

decoder = json.JSONDecoder()
for index, char in enumerate(text):
    if char != "{":
        continue
    try:
        obj, _ = decoder.raw_decode(text[index:])
    except Exception:
        continue
    if isinstance(obj, dict):
        print(json.dumps(obj, ensure_ascii=False))
        exit(0)

print("{}")
PY
}

parse_claude_metrics() {
  local input
  input=$(cat)
  __PARSE_INPUT="$input" python3 <<'PY'
import json
import os

raw = os.environ.get('__PARSE_INPUT', '').strip()
try:
    data = json.loads(raw) if raw else {}
except Exception:
    data = {}

def clamp_score(value):
    try:
        number = float(value)
    except Exception:
        return None
    if number < 0:
        number = 0.0
    if number > 10:
        number = 10.0
    return number

def format_score(value):
    number = clamp_score(value)
    if number is None:
        return "0"
    return f"{number:.2f}".rstrip("0").rstrip(".") or "0"

quality = clamp_score(data.get("overall_score"))
quality_value = "N/A" if quality is None else (f"{quality:.2f}".rstrip("0").rstrip(".") or "0")

improvements = data.get("improvements", "")
if isinstance(improvements, list):
    improvements = "; ".join(str(item).strip() for item in improvements if str(item).strip())
elif improvements is None:
    improvements = ""
else:
    improvements = str(improvements).strip()

improvements = improvements.replace("\n", " ").replace("\t", " ").strip()

fields = {
    "prompt_quality": format_score(data.get("prompt_quality", 0)),
    "structure_coherence": format_score(data.get("structure_coherence", 0)),
    "coverage": format_score(data.get("coverage", 0)),
    "documentation": format_score(data.get("documentation", 0)),
    "quality_score": quality_value,
    "improvements": improvements,
}

for key, value in fields.items():
    print(f"{key}\t{value}")
PY
}

extract_review_fields() {
  local input_json="$1"
  printf "%s" "$input_json" | python3 -c '
import json, sys
import base64
raw = sys.stdin.read().strip()
try:
    d = json.loads(raw) if raw else {}
except Exception:
    d = {}

def gs(obj, key):
    v = obj.get(key)
    if v is None:
        return None
    if isinstance(v, dict):
        score = v.get("score")
        if score is None:
            return None
        return score
    return None

def clamp(v, lo=0, hi=10):
    if v is None:
        return None
    try:
        n = float(v)
    except Exception:
        return None
    return max(lo, min(hi, n))

def fmt(v):
    if v is None:
        return ""
    return f"{v:.1f}".rstrip("0").rstrip(".") or "0"

def b64(v):
    return base64.b64encode((v or "").encode("utf-8")).decode("ascii")

sc = clamp(gs(d, "structural_completeness"))
sec = clamp(gs(d, "security_audit"))
wf = clamp(gs(d, "workflow_analysis"))
aq = clamp(gs(d, "agent_quality"))
agn = clamp(gs(d, "squad_agnosticism"))
cq = clamp(gs(d, "config_quality"))
pe = clamp(gs(d, "production_evidence"))

es = d.get("executive_summary", {})
if not isinstance(es, dict):
    es = {}
overall = clamp(es.get("overall_score"))
improvements = es.get("improvements", [])
if isinstance(improvements, list):
    improvements = "\n".join(str(x).strip() for x in improvements if str(x).strip())
else:
    improvements = str(improvements or "")
priority_fixes = es.get("priority_fixes", [])
if isinstance(priority_fixes, list):
    priority_fixes = "\n".join(str(x).strip() for x in priority_fixes if str(x).strip())
else:
    priority_fixes = str(priority_fixes or "")

fp = 0
sec_data = d.get("security_audit", {})
if isinstance(sec_data, dict):
    fp_val = sec_data.get("false_positive_count", 0)
    if isinstance(fp_val, (int, float)):
        fp = int(fp_val)
    else:
        checks = sec_data.get("checks", [])
        if isinstance(checks, list):
            fp = sum(1 for c in checks if isinstance(c, dict) and c.get("status", "").upper() == "FALSE_POSITIVE")

for k, v in [
    ("structural_completeness", fmt(sc)),
    ("security_audit", fmt(sec)),
    ("workflow_analysis", fmt(wf)),
    ("agent_quality", fmt(aq)),
    ("squad_agnosticism", fmt(agn)),
    ("config_quality", fmt(cq)),
    ("production_evidence", fmt(pe)),
    ("overall_score", fmt(overall)),
    ("improvements_b64", b64(improvements)),
    ("priority_fixes_b64", b64(priority_fixes)),
    ("false_positive_count", fp),
]:
    print(f"{k}\t{v}")
' 2>/dev/null || true
}

localize_review_json_for_report() {
  local input_json="$1"
  LOCALIZED_REPORT_AVAILABLE="false"

  if [[ -z "$input_json" ]] || [[ "$input_json" == "{}" ]]; then
    printf '%s' "$input_json"
    return 0
  fi

  if [[ "$REPORT_LANG_RESOLVED" == "$ANALYSIS_LANG" ]]; then
    LOCALIZED_REPORT_AVAILABLE="true"
    printf '%s' "$input_json"
    return 0
  fi

  local translate_prompt
  translate_prompt="Translate every human-readable string value in the JSON below to ${REPORT_LANGUAGE_NAME}.

Rules:
- Keep JSON keys exactly unchanged.
- Keep numeric values exactly unchanged.
- Keep booleans, nulls, arrays, and object structure exactly unchanged.
- Keep IDs like WF-001, AGENT-001, CONFIG-001, SEC-002 exactly unchanged.
- Keep machine statuses exactly unchanged when they are enum-like: PASS, FAIL, WARN, PARTIAL, FALSE_POSITIVE, REAL, CONDITIONAL.
- Translate only human-readable prose and labels.
- Output ONLY valid JSON.

JSON:
\`\`\`json
$input_json
\`\`\`"

  local translated_raw translated_json
  if translated_raw=$(run_llm_prompt_with_replan "$MODEL_QUALITY" "$translate_prompt" "${PROGRESS_LOG:-/dev/null}" "translate" 2>/dev/null); then
    translated_json=$(printf '%s' "$translated_raw" | extract_first_json_object)
    if [[ -n "$translated_json" ]] && [[ "$translated_json" != "{}" ]]; then
      LOCALIZED_REPORT_AVAILABLE="true"
      printf '%s' "$translated_json"
      return 0
    fi
  fi

  printf '%s' "$input_json"
}

extract_structure_fields() {
  local input_json="$1"
  printf "%s" "$input_json" | python3 -c '
import json, sys, base64
raw = sys.stdin.read().strip()
try:
    d = json.loads(raw) if raw else {}
except Exception:
    d = {}

coverage = d.get("coverage") or {}
def b64_join(items):
    if not isinstance(items, list):
        items = []
    text = "\n".join(str(x).strip() for x in items if str(x).strip())
    return base64.b64encode(text.encode("utf-8")).decode("ascii")

fields = {
    "squad_type": d.get("squad_type", "unknown"),
    "type_confidence": d.get("type_confidence", 0),
    "agents": coverage.get("agents", 0),
    "tasks": coverage.get("tasks", 0),
    "workflows": coverage.get("workflows", 0),
    "checklists": coverage.get("checklists", 0),
    "structure_valid": "true" if d.get("structure_valid") else "false",
    "blocking_issue_count": d.get("blocking_issue_count", 0),
    "warning_count": d.get("warning_count", 0),
    "security_issue_count": d.get("security_issue_count", 0),
    "non_security_blocking_count": d.get("non_security_blocking_count", 0),
    "blocking_issues_b64": b64_join(d.get("blocking_issues") or []),
    "warnings_b64": b64_join(d.get("warnings") or []),
}

for k, v in fields.items():
    print(f"{k}\t{v}")
' 2>/dev/null || true
}

extract_deep_analysis_payload() {
  local input_json="$1"
  printf "%s" "$input_json" | python3 -c '
import json, sys
raw = sys.stdin.read().strip()
try:
    d = json.loads(raw) if raw else {}
except Exception:
    d = {}
analysis = d.get("analysis", {})
if not isinstance(analysis, dict):
    analysis = {}
print(json.dumps(analysis))
' 2>/dev/null || printf '{}'
}

collect_orchestrator_baseline() {
  local config_version=""
  local readme_version=""
  local agent_version=""
  local version_mismatch=""
  local sc_pass=0
  local sc_total=2
  local lifecycle_pass=0
  local lifecycle_total=2
  local agent_quality_gaps=0

  M_AGENT_COUNT=$(find "$SQUAD_DIR/agents" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_TASK_COUNT=$(find "$SQUAD_DIR/tasks" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_CHECKLIST_COUNT=$(find "$SQUAD_DIR/checklists" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_TEMPLATE_COUNT=$(find "$SQUAD_DIR/templates" -type f 2>/dev/null | wc -l | tr -d ' ')
  M_DATA_COUNT=$(find "$SQUAD_DIR/data" -type f 2>/dev/null | wc -l | tr -d ' ')
  M_TOTAL_LINES=$(find "$SQUAD_DIR" -type f \( -name "*.md" -o -name "*.yaml" \) -exec cat {} + 2>/dev/null | wc -l | tr -d ' ')

  ENTRY_AGENT=""
  if [[ -f "$SQUAD_DIR/config.yaml" ]]; then
    if grep -q "entry_agent:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      ENTRY_AGENT=$(grep "entry_agent:" "$SQUAD_DIR/config.yaml" | head -1 | sed 's/.*entry_agent:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs)
    elif grep -qE "^[[:space:]]+- id:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      ENTRY_AGENT=$(grep -E "^[[:space:]]+- id:" "$SQUAD_DIR/config.yaml" | head -1 | sed 's/.*- id:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs)
    fi
  fi

  CONFIG_TASK_IDS=$(awk '
    /^tasks:/ { in_tasks=1; next }
    in_tasks && /^[^[:space:]]/ { in_tasks=0 }
    in_tasks && $1 == "-" && $2 == "id:" {
      gsub(/"/, "", $3)
      print $3
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true)

  M_HAS_TESTED_FLAG="false"
  if grep -qE "^tested:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
    sc_pass=$((sc_pass + 1))
    M_HAS_TESTED_FLAG="true"
  fi

  M_HAS_ARCHITECTURE_DOC="false"
  if [[ -f "$SQUAD_DIR/ARCHITECTURE.md" ]]; then
    sc_pass=$((sc_pass + 1))
    M_HAS_ARCHITECTURE_DOC="true"
  fi

  M_HAS_UPDATE_TASK="false"
  if [[ -d "$SQUAD_DIR/tasks" ]]; then
    local update_tasks
    update_tasks=$(find "$SQUAD_DIR/tasks" -maxdepth 1 -name "update-*.md" 2>/dev/null | wc -l | tr -d ' ')
    if [[ "$update_tasks" -gt 0 ]]; then
      lifecycle_pass=$((lifecycle_pass + 1))
      M_HAS_UPDATE_TASK="true"
    fi
  fi

  M_HAS_DELETE_TASK="false"
  if [[ -d "$SQUAD_DIR/tasks" ]]; then
    local delete_tasks
    delete_tasks=$(find "$SQUAD_DIR/tasks" -maxdepth 1 -name "delete-*.md" 2>/dev/null | wc -l | tr -d ' ')
    if [[ "$delete_tasks" -gt 0 ]]; then
      lifecycle_pass=$((lifecycle_pass + 1))
      M_HAS_DELETE_TASK="true"
    fi
  fi

  M_STRUCT_COMPLETENESS_PASS=$sc_pass
  M_STRUCT_COMPLETENESS_TOTAL=$sc_total
  M_CONTEXTUAL_LIFECYCLE_PASS=$lifecycle_pass
  M_CONTEXTUAL_LIFECYCLE_TOTAL=$lifecycle_total
  M_CONTEXTUAL_LIFECYCLE_WARNINGS=$((lifecycle_total - lifecycle_pass))

  M_VERSION_CONSISTENT="true"
  M_VERSION_DETAILS=""
  config_version=$(grep -E "^version:" "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/version:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs 2>/dev/null || true)
  if [[ -z "$config_version" ]]; then
    config_version=$(grep -E "^[[:space:]]+version:" "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/.*version:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs 2>/dev/null || true)
  fi
  if [[ -f "$SQUAD_DIR/README.md" ]]; then
    readme_version=$(grep -oE "[Vv]ersion[[:space:]]*:?[[:space:]]*[0-9]+\.[0-9]+(\.[0-9]+)?" "$SQUAD_DIR/README.md" 2>/dev/null | head -1 | grep -oE "[0-9]+\.[0-9]+(\.[0-9]+)?" || true)
  fi
  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    local agent_file=""
    if [[ -f "$SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      agent_file="$SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    elif [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      agent_file="$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    fi
    if [[ -n "$agent_file" ]]; then
      agent_version=$(grep -oE "[Vv]ersion[[:space:]]*:?[[:space:]]*[0-9]+\.[0-9]+(\.[0-9]+)?" "$agent_file" 2>/dev/null | head -1 | grep -oE "[0-9]+\.[0-9]+(\.[0-9]+)?" || true)
    fi
  fi
  if [[ -n "$config_version" ]]; then
    if [[ -n "$readme_version" ]] && [[ "$readme_version" != "$config_version" ]]; then
      version_mismatch="config=$config_version vs README=$readme_version"
      M_VERSION_CONSISTENT="false"
    fi
    if [[ -n "$agent_version" ]] && [[ "$agent_version" != "$config_version" ]]; then
      version_mismatch="${version_mismatch:+$version_mismatch; }config=$config_version vs agent=$agent_version"
      M_VERSION_CONSISTENT="false"
    fi
  else
    M_VERSION_CONSISTENT="unknown"
  fi
  M_VERSION_DETAILS="$version_mismatch"

  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    local entry_agent_file=""
    if [[ -f "$SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      entry_agent_file="$SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    elif [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      entry_agent_file="$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    fi
    if [[ -n "$entry_agent_file" ]]; then
      grep -qiE "smoke.?tests?" "$entry_agent_file" 2>/dev/null || agent_quality_gaps=$((agent_quality_gaps + 1))
      grep -qiE "output.?examples?" "$entry_agent_file" 2>/dev/null || agent_quality_gaps=$((agent_quality_gaps + 1))
      grep -qiE "anti.?patterns?" "$entry_agent_file" 2>/dev/null || agent_quality_gaps=$((agent_quality_gaps + 1))
      grep -qiE "heuristic" "$entry_agent_file" 2>/dev/null || agent_quality_gaps=$((agent_quality_gaps + 1))
      grep -qiE "handoff" "$entry_agent_file" 2>/dev/null || agent_quality_gaps=$((agent_quality_gaps + 1))
    fi
  fi
  M_AGENT_QUALITY_GAPS=$agent_quality_gaps
}

hydrate_deep_review_from_envelope() {
  local deep_envelope="$1"
  local analysis_json=""
  local parsed_scores=""

  analysis_json=$(extract_deep_analysis_payload "$deep_envelope")
  CLAUDE_RAW_JSON="$analysis_json"
  CLAUDE_REPORT_JSON=$(localize_review_json_for_report "$analysis_json")

  parsed_scores=$(extract_review_fields "$analysis_json")
  while IFS=$'\t' read -r key value; do
    case "$key" in
      structural_completeness) CLAUDE_STRUCTURAL_COMPLETENESS="$value" ;;
      security_audit) CLAUDE_SECURITY_AUDIT="$value" ;;
      workflow_analysis) CLAUDE_WORKFLOW_ANALYSIS="$value" ;;
      agent_quality) CLAUDE_AGENT_QUALITY="$value" ;;
      squad_agnosticism) CLAUDE_SQUAD_AGNOSTICISM="$value" ;;
      config_quality) CLAUDE_CONFIG_QUALITY="$value" ;;
      production_evidence) CLAUDE_PRODUCTION_EVIDENCE="$value" ;;
      overall_score) M_QUALITY_SCORE="$value" ;;
      improvements_b64)
        M_IMPROVEMENTS=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
        M_IMPROVEMENTS_REPORT="$M_IMPROVEMENTS"
        ;;
      priority_fixes_b64)
        CLAUDE_EXEC_SUMMARY=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
        CLAUDE_EXEC_SUMMARY_REPORT="$CLAUDE_EXEC_SUMMARY"
        ;;
      false_positive_count)
        local fp_count="${value%%.*}"
        if [[ "$fp_count" =~ ^[0-9]+$ ]] && [[ "$fp_count" -gt 0 ]]; then
          local adjusted=$((SEC_FAIL - fp_count))
          if [[ $adjusted -lt 0 ]]; then adjusted=0; fi
          SEC_FAIL=$adjusted
        fi
        ;;
    esac
  done <<< "$parsed_scores"

  if ! is_numeric_score "${M_QUALITY_SCORE:-}"; then
    M_QUALITY_SCORE="N/A"
  else
    M_QUALITY_SCORE=$(clamp_score_0_10 "$M_QUALITY_SCORE")
  fi
}

extract_declared_output_root() {
  local shared_output_root=""
  local base_path_line=""
  local raw_root=""
  local trimmed=""

  shared_output_root=$(awk '
    BEGIN { in_distribution=0 }
    /^distribution_contract:[[:space:]]*$/ { in_distribution=1; next }
    in_distribution && /^[^[:space:]]/ { in_distribution=0 }
    in_distribution && /^[[:space:]]*shared_safe_outputs_root:[[:space:]]*/ {
      gsub(/^[[:space:]]*shared_safe_outputs_root:[[:space:]]*/, "", $0)
      gsub(/["'\'']/, "", $0)
      gsub(/[[:space:]]+$/, "", $0)
      print $0
      exit
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true)

  if [[ -n "$shared_output_root" ]]; then
    raw_root="$shared_output_root"
  else
    base_path_line=$(grep -E '^[[:space:]]*base_path:[[:space:]]*' "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 || true)
    [[ -z "$base_path_line" ]] && return 1
    raw_root=$(printf "%s" "$base_path_line" | sed 's/^[^:]*:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs)
  fi

  [[ -z "$raw_root" ]] && return 1

  trimmed="${raw_root%%\{*}"
  trimmed="${trimmed#./}"
  trimmed="${trimmed%/}"

  [[ -z "$trimmed" ]] && return 1
  printf "%s\n" "$trimmed"
}

count_declared_output_files() {
  local output_root=""
  output_root=$(extract_declared_output_root) || return 1

  local absolute_root="$WORKSPACE_ROOT/$output_root"
  [[ ! -d "$absolute_root" ]] && return 1

  find "$absolute_root" -type f 2>/dev/null | wc -l | tr -d ' '
}

count_usage_evidence_output_files() {
  local output_root=""
  output_root=$(extract_declared_output_root) || return 1

  local absolute_root="$WORKSPACE_ROOT/$output_root"
  [[ ! -d "$absolute_root" ]] && return 1

  find "$absolute_root" -type f \
    ! -path '*/.*' \
    ! -name '.DS_Store' \
    2>/dev/null | wc -l | tr -d ' '
}

extract_config_scalar() {
  local key="$1"
  awk -v key="$key" '
    $0 ~ ("^" key ":[[:space:]]*") {
      sub(/^[^:]+:[[:space:]]*/, "", $0)
      gsub(/["'\'']/, "", $0)
      gsub(/[[:space:]]+$/, "", $0)
      print $0
      exit
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true
}

extract_workspace_integration_level() {
  awk '
    BEGIN { in_ws=0 }
    /^workspace_integration_level:[[:space:]]*/ {
      gsub(/^workspace_integration_level:[[:space:]]*/, "", $0);
      gsub(/["'\'']/, "", $0);
      gsub(/[[:space:]]/, "", $0);
      print $0;
      exit;
    }
    /^workspace_integration:[[:space:]]*$/ { in_ws=1; next }
    in_ws && /^[^[:space:]]/ { in_ws=0 }
    in_ws && /^[[:space:]]*level:[[:space:]]*/ {
      gsub(/^[[:space:]]*level:[[:space:]]*/, "", $0);
      gsub(/["'\'']/, "", $0);
      gsub(/[[:space:]]/, "", $0);
      print $0;
      exit;
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true
}

collect_agnosticism_excluded_dirs() {
  python3 - "$SQUAD_DIR/config.yaml" <<'PY'
import sys
from pathlib import Path

import yaml

config_path = Path(sys.argv[1])
if not config_path.exists():
    raise SystemExit(0)

raw = yaml.safe_load(config_path.read_text(encoding="utf-8")) or {}
items = raw.get("agnosticism_exceptions") or []
seen = set()

for item in items:
    if not isinstance(item, dict):
        continue
    scope = item.get("scope")
    if not isinstance(scope, str) or "/" not in scope:
        continue
    head = scope.split("/", 1)[0].strip()
    if not head or "*" in head or head in seen:
        continue
    seen.add(head)
    print(head)
PY
}

count_contract_test_files() {
  local test_count=0
  local infra_count=0
  local slug_hyphen="$SQUAD_NAME"
  local slug_underscore="${SQUAD_NAME//-/_}"

  if [[ -d "$SQUAD_DIR/tests" ]]; then
    test_count=$(find "$SQUAD_DIR/tests" -type f \( -name "*.bats" -o -name "*.cjs" -o -name "*.js" -o -name "*.mjs" \) 2>/dev/null | wc -l | tr -d ' ')
  fi

  infra_count=$(find "$WORKSPACE_ROOT/infrastructure/scripts/squads" -type f \
    \( -name "*${slug_hyphen}*.cjs" -o -name "*${slug_hyphen}*.js" -o -name "*${slug_hyphen}*.mjs" \
       -o -name "*${slug_underscore}*.cjs" -o -name "*${slug_underscore}*.js" -o -name "*${slug_underscore}*.mjs" \) \
    2>/dev/null | wc -l | tr -d ' ')

  echo $((test_count + infra_count))
}

count_operational_story_files() {
  local roots=()
  local count=0

  [[ -d "$WORKSPACE_ROOT/docs/stories" ]] && roots+=("$WORKSPACE_ROOT/docs/stories")
  [[ -d "$SQUAD_DIR/docs/stories" ]] && roots+=("$SQUAD_DIR/docs/stories")

  if [[ ${#roots[@]} -eq 0 ]]; then
    echo 0
    return 0
  fi

  count=$(grep -RIlE --include="*.md" \
    "(${SQUAD_NAME}|squads/${SQUAD_NAME}/|validate-squad[[:space:]]+${SQUAD_NAME}|test_[[:alnum:]_-]*${SQUAD_NAME//-/_})" \
    "${roots[@]}" 2>/dev/null | wc -l | tr -d ' ')

  echo "$count"
}

parse_workflow_contract_totals() {
  node -e '
const fs = require("fs");
const raw = fs.readFileSync(0, "utf8").trim();
const ansiStripped = raw.replace(/\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])/g, "");

function extractFirstJsonObject(text) {
  for (let start = 0; start < text.length; start += 1) {
    if (text[start] !== "{") continue;
    let depth = 0;
    let inString = false;
    let escaped = false;
    for (let i = start; i < text.length; i += 1) {
      const ch = text[i];
      if (inString) {
        if (escaped) {
          escaped = false;
        } else if (ch === "\\\\") {
          escaped = true;
        } else if (ch === "\"") {
          inString = false;
        }
        continue;
      }
      if (ch === "\"") {
        inString = true;
        continue;
      }
      if (ch === "{") depth += 1;
      if (ch === "}") {
        depth -= 1;
        if (depth === 0) return text.slice(start, i + 1);
      }
    }
}
  return "{}";
}

let data = {};
const firstObject = extractFirstJsonObject(ansiStripped);
try {
  data = firstObject ? JSON.parse(firstObject) : {};
} catch {
  data = {};
}
const totals = data.totals || {};
const fields = {
  files_checked: Number(totals.files_checked) || 0,
  errors: Number(totals.errors) || 0,
  warnings: Number(totals.warnings) || 0,
  invalid_files: Number(totals.invalid_files) || 0,
};
for (const [key, value] of Object.entries(fields)) {
  console.log(`${key}\t${value}`);
}
'
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 1: STRUCTURE (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_structure() {
  log_section "PHASE 1: Structure Validation (Bash)"
  local tier1_fail=0

  # 1.1 Config file
  log_subsection "1.1 Configuration"
  if [[ -f "$SQUAD_DIR/config.yaml" ]]; then
    log_pass "config.yaml exists"

    # Check for name (top-level or under squad:/pack:)
    if grep -qE "^name:|^[[:space:]]+name:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      log_pass "config.yaml has 'name' field"
    else
      log_fail "config.yaml missing 'name' field"
      tier1_fail=$((tier1_fail + 1))
    fi

    # Check for version (top-level or under squad:/pack:)
    if grep -qE "^version:|^[[:space:]]+version:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      log_pass "config.yaml has 'version' field"
    else
      log_fail "config.yaml missing 'version' field"
      tier1_fail=$((tier1_fail + 1))
    fi

    # Check for entry_agent (top-level, under squad:/pack:, or in agents list)
    if grep -q "entry_agent:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      log_pass "config.yaml has 'entry_agent' field"
      ENTRY_AGENT=$(grep "entry_agent:" "$SQUAD_DIR/config.yaml" | head -1 | sed 's/.*entry_agent:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs)
    elif grep -qE "^[[:space:]]+- id:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      # Has agents list, extract first agent as entry point
      ENTRY_AGENT=$(grep -E "^[[:space:]]+- id:" "$SQUAD_DIR/config.yaml" | head -1 | sed 's/.*- id:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs)
      log_warn "No entry_agent defined, using first agent: $ENTRY_AGENT"
    else
      log_warn "config.yaml missing 'entry_agent' field (non-blocking)"
    fi
  else
    log_fail "config.yaml not found"
    tier1_fail=$((tier1_fail + 1))
  fi

  # 1.2 Entry agent
  log_subsection "1.2 Entry Point"
  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    if asset_exists "agents" "${ENTRY_AGENT}.md"; then
      log_pass "Entry agent exists: agents/${ENTRY_AGENT}.md"
    else
      log_fail "Entry agent not found: agents/${ENTRY_AGENT}.md"
      tier1_fail=$((tier1_fail + 1))
    fi
  fi

  # 1.2b Config task registry integrity
  local config_task_ids=""
  config_task_ids=$(awk '
    /^tasks:/ { in_tasks=1; next }
    in_tasks && /^[^[:space:]]/ { in_tasks=0 }
    in_tasks && $1 == "-" && $2 == "id:" {
      gsub(/"/, "", $3)
      print $3
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true)
  if [[ -n "$config_task_ids" ]]; then
    CONFIG_TASK_IDS="$config_task_ids"
    local missing_config_tasks=0
    while IFS= read -r task_id; do
      [[ -n "$task_id" ]] || continue
      if [[ -f "$SQUAD_DIR/tasks/${task_id}.md" ]]; then
        log_pass "CONFIG-002: Task declared in config exists: $task_id"
      else
        log_fail "CONFIG-002: Task declared in config missing file: $task_id"
        tier1_fail=$((tier1_fail + 1))
        missing_config_tasks=$((missing_config_tasks + 1))
      fi
    done <<< "$config_task_ids"
    if [[ "$missing_config_tasks" -eq 0 ]]; then
      log_pass "CONFIG-002: Config task registry has no ghost task IDs"
    fi
  fi

  # 1.3 Workspace integration governance
  log_subsection "1.3 Workspace Integration Governance"
  local workspace_level=""
  workspace_level=$(awk '
    BEGIN { in_ws=0 }
    /^workspace_integration_level:[[:space:]]*/ {
      gsub(/^workspace_integration_level:[[:space:]]*/, "", $0);
      gsub(/["'\'']/, "", $0);
      gsub(/[[:space:]]/, "", $0);
      print $0;
      exit;
    }
    /^workspace_integration:[[:space:]]*$/ { in_ws=1; next }
    in_ws && /^[^[:space:]]/ { in_ws=0 }
    in_ws && /^[[:space:]]*level:[[:space:]]*/ {
      gsub(/^[[:space:]]*level:[[:space:]]*/, "", $0);
      gsub(/["'\'']/, "", $0);
      gsub(/[[:space:]]/, "", $0);
      print $0;
      exit;
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true)

  case "$workspace_level" in
    none|read_only|controlled_runtime_consumer|workspace_first)
      log_pass "workspace integration level declared: $workspace_level"
      ;;
    "")
      log_fail "config.yaml missing workspace integration level (workspace_integration.level)"
      tier1_fail=$((tier1_fail + 1))
      ;;
    *)
      log_fail "invalid workspace integration level: '$workspace_level'"
      tier1_fail=$((tier1_fail + 1))
      ;;
  esac

  if [[ -n "$workspace_level" && "$workspace_level" != "none" ]]; then
    # Build list of existing paths to search (avoid rg exit 2 on missing files)
    local ws_search_paths=()
    [[ -d "$SQUAD_DIR/agents" ]] && ws_search_paths+=("$SQUAD_DIR/agents")
    [[ -d "$SQUAD_DIR/tasks" ]] && ws_search_paths+=("$SQUAD_DIR/tasks")
    [[ -d "$SQUAD_DIR/workflows" ]] && ws_search_paths+=("$SQUAD_DIR/workflows")
    [[ -f "$SQUAD_DIR/config.yaml" ]] && ws_search_paths+=("$SQUAD_DIR/config.yaml")

    if [[ ${#ws_search_paths[@]} -gt 0 ]] && grep -rn "workspace/" "${ws_search_paths[@]}" >/dev/null 2>&1; then
      log_pass "workspace references found for integration level '$workspace_level'"
    else
      log_fail "workspace integration level '$workspace_level' declared but no workspace paths found"
      tier1_fail=$((tier1_fail + 1))
    fi
  fi

  if [[ "$workspace_level" == "controlled_runtime_consumer" || "$workspace_level" == "workspace_first" ]]; then
    if [[ -d "$C_LEVEL_WORKSPACE_DIR" ]]; then
      log_pass "workspace governance squad present for level '$workspace_level'"
    else
      log_fail "workspace level '$workspace_level' requires workspace governance squad (squads/c-level) to exist"
      tier1_fail=$((tier1_fail + 1))
    fi
    # Build list of existing paths (README.md may not exist yet)
    local coo_search_paths=()
    [[ -f "$SQUAD_DIR/README.md" ]] && coo_search_paths+=("$SQUAD_DIR/README.md")
    [[ -d "$SQUAD_DIR/tasks" ]] && coo_search_paths+=("$SQUAD_DIR/tasks")
    [[ -d "$SQUAD_DIR/workflows" ]] && coo_search_paths+=("$SQUAD_DIR/workflows")
    [[ -f "$SQUAD_DIR/config.yaml" ]] && coo_search_paths+=("$SQUAD_DIR/config.yaml")

    if [[ ${#coo_search_paths[@]} -gt 0 ]] && grep -rn -E "@coo|COO|c-level|workspace-chief|readiness_owner|workspace-handoff\\.yaml|handoff.*workspace" \
      "${coo_search_paths[@]}" >/dev/null 2>&1; then
      log_pass "workspace write integration delegates to workspace governance"
    else
      log_fail "workspace level '$workspace_level' requires explicit COO/workspace governance handoff"
      tier1_fail=$((tier1_fail + 1))
    fi
  fi

  if [[ "$workspace_level" == "workspace_first" ]]; then
    local bootstrap_count=0
    local essentials_count=0
    bootstrap_count=$(find "$SQUAD_DIR/scripts" -maxdepth 1 -type f -name "bootstrap-*-workspace.sh" 2>/dev/null | wc -l | tr -d ' ')
    essentials_count=$(find "$SQUAD_DIR/scripts" -maxdepth 1 -type f -name "validate-*-essentials.sh" 2>/dev/null | wc -l | tr -d ' ')
    if [[ "$bootstrap_count" -gt 0 ]]; then
      log_pass "workspace_first has bootstrap script"
    else
      log_fail "workspace_first requires scripts/bootstrap-*-workspace.sh"
      tier1_fail=$((tier1_fail + 1))
    fi
    if [[ "$essentials_count" -gt 0 ]]; then
      log_pass "workspace_first has essentials validator script"
    else
      log_fail "workspace_first requires scripts/validate-*-essentials.sh"
      tier1_fail=$((tier1_fail + 1))
    fi
  fi

  # 1.4 Directory structure
  log_subsection "1.4 Directory Structure"
  local found_dirs=0
  for dir in agents tasks checklists templates data; do
    if [[ -d "$SQUAD_DIR/$dir" ]]; then
      local count=$(find "$SQUAD_DIR/$dir" -type f \( -name "*.md" -o -name "*.yaml" -o -name "*.yml" \) 2>/dev/null | wc -l | tr -d ' ')
      log_pass "$dir/ exists ($count files)"
      found_dirs=$((found_dirs + 1))
    else
      log_info "$dir/ not found (optional)"
    fi
  done

  # 1.5 Collect metrics
  log_subsection "1.5 Metrics Collection"
  M_AGENT_COUNT=$(find "$SQUAD_DIR/agents" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_TASK_COUNT=$(find "$SQUAD_DIR/tasks" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_CHECKLIST_COUNT=$(find "$SQUAD_DIR/checklists" -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
  M_TEMPLATE_COUNT=$(find "$SQUAD_DIR/templates" -type f 2>/dev/null | wc -l | tr -d ' ')
  M_DATA_COUNT=$(find "$SQUAD_DIR/data" -type f 2>/dev/null | wc -l | tr -d ' ')
  M_TOTAL_LINES=$(find "$SQUAD_DIR" -type f \( -name "*.md" -o -name "*.yaml" \) -exec cat {} + 2>/dev/null | wc -l | tr -d ' ')

  log_info "Agents: $M_AGENT_COUNT, Tasks: $M_TASK_COUNT, Checklists: $M_CHECKLIST_COUNT"
  log_info "Total lines: $M_TOTAL_LINES"

  # 1.6 Stub/placeholder guard (ghost artifacts)
  log_subsection "1.6 Stub/Placeholder Guard"
  local stub_hits=0
  local stub_scope=(
    "$SQUAD_DIR/agents"
    "$SQUAD_DIR/tasks"
    "$SQUAD_DIR/checklists"
    "$SQUAD_DIR/templates"
    "$SQUAD_DIR/workflows"
    "$SQUAD_DIR/data"
  )
  local stub_matches
  stub_matches=$(grep -RInE --include="*.md" --include="*.yaml" --include="*.yml" \
    "(TODO for later completion|AUTO-GENERATED STUB|\\[STUB\\]|placeholder artifact|stub file)" \
    "${stub_scope[@]}" 2>/dev/null || true)
  if [[ -n "$stub_matches" ]]; then
    log_fail "STRUCT-007: Stub/placeholder artifacts found (remove placeholders before PASS)"
    tier1_fail=$((tier1_fail + 1))
    if [[ "$VERBOSE" == "true" ]]; then
      echo "$stub_matches" | head -n 10
    fi
  else
    log_pass "STRUCT-007: No stub/placeholder artifact markers found"
  fi

  # 1.7 Structural Completeness (SC_STRUCT_001)
  log_subsection "1.7 Structural Completeness (SC_STRUCT_001)"
  local sc_pass=0
  local sc_total=2

  # Check tested: flag in config.yaml
  if grep -qE "^tested:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
    log_pass "SC_STRUCT_001: tested: flag present in config.yaml"
    sc_pass=$((sc_pass + 1))
    M_HAS_TESTED_FLAG="true"
  else
    log_warn "SC_STRUCT_001: Missing tested: flag in config.yaml"
  fi

  # Check ARCHITECTURE.md exists
  if [[ -f "$SQUAD_DIR/ARCHITECTURE.md" ]]; then
    log_pass "SC_STRUCT_001: ARCHITECTURE.md exists"
    sc_pass=$((sc_pass + 1))
    M_HAS_ARCHITECTURE_DOC="true"
  else
    log_warn "SC_STRUCT_001: Missing ARCHITECTURE.md"
  fi

  # Check update-*.md task exists
  local has_update_task=false
  local lifecycle_pass=0
  local lifecycle_total=2
  if [[ -d "$SQUAD_DIR/tasks" ]]; then
    local update_tasks
    update_tasks=$(find "$SQUAD_DIR/tasks" -maxdepth 1 -name "update-*.md" 2>/dev/null | wc -l | tr -d ' ')
    if [[ "$update_tasks" -gt 0 ]]; then
      log_pass "SC_STRUCT_001: update-*.md task exists ($update_tasks found, lifecycle contextual)"
      has_update_task=true
      lifecycle_pass=$((lifecycle_pass + 1))
      M_HAS_UPDATE_TASK="true"
    fi
  fi
  if [[ "$has_update_task" == "false" ]]; then
    log_warn "SC_STRUCT_001: Missing update-*.md task (contextual lifecycle warning, not structural debt)"
  fi

  # Check delete-*.md task exists
  local has_delete_task=false
  if [[ -d "$SQUAD_DIR/tasks" ]]; then
    local delete_tasks
    delete_tasks=$(find "$SQUAD_DIR/tasks" -maxdepth 1 -name "delete-*.md" 2>/dev/null | wc -l | tr -d ' ')
    if [[ "$delete_tasks" -gt 0 ]]; then
      log_pass "SC_STRUCT_001: delete-*.md task exists ($delete_tasks found, lifecycle contextual)"
      has_delete_task=true
      lifecycle_pass=$((lifecycle_pass + 1))
      M_HAS_DELETE_TASK="true"
    fi
  fi
  if [[ "$has_delete_task" == "false" ]]; then
    log_warn "SC_STRUCT_001: Missing delete-*.md task (contextual lifecycle warning, not structural debt)"
  fi

  M_STRUCT_COMPLETENESS_PASS=$sc_pass
  M_STRUCT_COMPLETENESS_TOTAL=$sc_total
  M_CONTEXTUAL_LIFECYCLE_PASS=$lifecycle_pass
  M_CONTEXTUAL_LIFECYCLE_TOTAL=$lifecycle_total
  M_CONTEXTUAL_LIFECYCLE_WARNINGS=$((lifecycle_total - lifecycle_pass))
  log_info "Structural completeness: $sc_pass/$sc_total"

  # 1.8 Version Consistency
  log_subsection "1.8 Version Consistency"
  local config_version=""
  local readme_version=""
  local agent_version=""
  local version_mismatch=""

  # Try root-level first (brand style), then nested under squad:/pack: (books/copy/hormozi style)
  config_version=$(grep -E "^version:" "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/version:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs 2>/dev/null || true)
  if [[ -z "$config_version" ]]; then
    config_version=$(grep -E "^[[:space:]]+version:" "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/.*version:[[:space:]]*//' | tr -d '"' | tr -d "'" | xargs 2>/dev/null || true)
  fi

  if [[ -f "$SQUAD_DIR/README.md" ]]; then
    readme_version=$(grep -oE "[Vv]ersion[[:space:]]*:?[[:space:]]*[0-9]+\.[0-9]+(\.[0-9]+)?" "$SQUAD_DIR/README.md" 2>/dev/null | head -1 | grep -oE "[0-9]+\.[0-9]+(\.[0-9]+)?" || true)
  fi

  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    local agent_file=""
    if [[ -f "$SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      agent_file="$SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    elif [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      agent_file="$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    fi
    if [[ -n "$agent_file" ]]; then
      agent_version=$(grep -oE "[Vv]ersion[[:space:]]*:?[[:space:]]*[0-9]+\.[0-9]+(\.[0-9]+)?" "$agent_file" 2>/dev/null | head -1 | grep -oE "[0-9]+\.[0-9]+(\.[0-9]+)?" || true)
    fi
  fi

  if [[ -n "$config_version" ]]; then
    log_info "config.yaml version: $config_version"
    if [[ -n "$readme_version" ]] && [[ "$readme_version" != "$config_version" ]]; then
      log_warn "Version mismatch: config.yaml=$config_version, README.md=$readme_version"
      version_mismatch="config=$config_version vs README=$readme_version"
      M_VERSION_CONSISTENT="false"
    fi
    if [[ -n "$agent_version" ]] && [[ "$agent_version" != "$config_version" ]]; then
      log_warn "Version mismatch: config.yaml=$config_version, entry agent=$agent_version"
      version_mismatch="${version_mismatch:+$version_mismatch; }config=$config_version vs agent=$agent_version"
      M_VERSION_CONSISTENT="false"
    fi
    if [[ "$M_VERSION_CONSISTENT" == "true" ]]; then
      log_pass "Version consistent across sources"
    fi
  else
    log_warn "No version found in config.yaml to compare"
    M_VERSION_CONSISTENT="unknown"
  fi
  M_VERSION_DETAILS="$version_mismatch"

  # 1.9 Agent Structure (Entry Agent)
  log_subsection "1.9 Agent Structure (Entry Agent)"
  local agent_quality_gaps=0
  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    local entry_agent_file=""
    if [[ -f "$SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      entry_agent_file="$SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    elif [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      entry_agent_file="$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    fi

    if [[ -n "$entry_agent_file" ]]; then
      # Check for smoke_tests / smoke-tests
      if grep -qiE "smoke.?tests?" "$entry_agent_file" 2>/dev/null; then
        log_pass "Entry agent has smoke_tests section"
      else
        log_warn "Entry agent missing smoke_tests section"
        agent_quality_gaps=$((agent_quality_gaps + 1))
      fi

      # Check for output_examples / output-examples
      if grep -qiE "output.?examples?" "$entry_agent_file" 2>/dev/null; then
        log_pass "Entry agent has output_examples section"
      else
        log_warn "Entry agent missing output_examples section"
        agent_quality_gaps=$((agent_quality_gaps + 1))
      fi

      # Check for anti_patterns / anti-patterns
      if grep -qiE "anti.?patterns?" "$entry_agent_file" 2>/dev/null; then
        log_pass "Entry agent has anti_patterns section"
      else
        log_warn "Entry agent missing anti_patterns section"
        agent_quality_gaps=$((agent_quality_gaps + 1))
      fi

      # Check for heuristics (with WHEN/SE/QUANDO)
      if grep -qiE "heuristic" "$entry_agent_file" 2>/dev/null; then
        log_pass "Entry agent has heuristics section"
      else
        log_warn "Entry agent missing heuristics section"
        agent_quality_gaps=$((agent_quality_gaps + 1))
      fi

      # Check for handoff_to / handoffs
      if grep -qiE "handoff" "$entry_agent_file" 2>/dev/null; then
        log_pass "Entry agent has handoff section"
      else
        log_warn "Entry agent missing handoff section"
        agent_quality_gaps=$((agent_quality_gaps + 1))
      fi
    fi
  fi
  M_AGENT_QUALITY_GAPS=$agent_quality_gaps
  log_info "Agent quality gaps: $agent_quality_gaps/5"

  # 1.10 pack: section check (CI parity — same check as CI validate-squads)
  log_subsection "1.10 pack: Section Check (CI Parity)"
  local config="$SQUAD_DIR/config.yaml"
  if [[ -f "$config" ]]; then
    if grep -q "^pack:" "$config"; then
      log_pass "CI-PAR-001: config.yaml has 'pack:' section"
    else
      log_fail "CI-PAR-001: config.yaml missing 'pack:' section (CI hard-mandatory)"
      tier1_fail=$((tier1_fail + 1))
    fi
  fi

  # 1.11 YAML syntax check (CI parity — mirrors GrantBirki json-yaml-validate action)
  log_subsection "1.11 YAML Syntax Validation (CI Parity)"
  if command -v python3 >/dev/null 2>&1 && python3 -c "import yaml" 2>/dev/null; then
    local yaml_errors=0
    while IFS= read -r yaml_file; do
      [[ -z "$yaml_file" ]] && continue
      local yaml_err
      yaml_err=$(python3 -c "
import yaml, sys
try:
    yaml.safe_load(open('$yaml_file'))
except yaml.YAMLError as e:
    print(str(e))
    sys.exit(1)
" 2>&1) || {
        log_fail "CI-PAR-002: Invalid YAML syntax: $yaml_file — $yaml_err"
        tier1_fail=$((tier1_fail + 1))
        yaml_errors=$((yaml_errors + 1))
      }
    done < <(find "$SQUAD_DIR" -name "*.yaml" -o -name "*.yml" 2>/dev/null)
    if [[ "$yaml_errors" -eq 0 ]]; then
      log_pass "CI-PAR-002: All YAML files have valid syntax"
    fi
  else
    log_warn "CI-PAR-002: python3/pyyaml not available — YAML syntax check skipped (install python3 + pyyaml for full CI parity)"
  fi

  TIER1_FAIL=$tier1_fail
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 2: SECURITY SCAN (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_security() {
  log_section "PHASE 2: Security Scan (Bash)"
  local sec_fail=0

  log_subsection "2.1 API Keys & Tokens"

  if [[ -n "$(scan_dir_api_keys "$SQUAD_DIR")" ]]; then
    log_fail "SEC-001: Potential API keys found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-001: No hardcoded API keys"
  fi

  if [[ -n "$(scan_dir_secrets "$SQUAD_DIR")" ]]; then
    log_fail "SEC-002: Potential secrets found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-002: No hardcoded secrets"
  fi

  log_subsection "2.2 Cloud Credentials"

  if [[ -n "$(scan_dir_aws_keys "$SQUAD_DIR")" ]]; then
    log_fail "SEC-003: AWS Access Key found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-003: No AWS Access Keys"
  fi

  if [[ -n "$(scan_dir_gcp_service_accounts "$SQUAD_DIR")" ]]; then
    log_fail "SEC-004: GCP Service Account found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-004: No GCP Service Accounts"
  fi

  log_subsection "2.3 Private Keys"

  if [[ -n "$(scan_dir_private_keys "$SQUAD_DIR")" ]]; then
    log_fail "SEC-005: Private key content found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-005: No private key content"
  fi

  if [[ -n "$(scan_dir_key_files "$SQUAD_DIR")" ]]; then
    log_fail "SEC-006: Private key files found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-006: No private key files"
  fi

  log_subsection "2.4 Database & Sensitive Files"

  if [[ -n "$(scan_dir_db_urls "$SQUAD_DIR")" ]]; then
    log_fail "SEC-007: Database URL with password found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-007: No database URLs with passwords"
  fi

  if [[ -n "$(scan_dir_env_files "$SQUAD_DIR")" ]]; then
    log_fail "SEC-008: .env files found"
    sec_fail=$((sec_fail + 1))
  else
    log_pass "SEC-008: No .env files"
  fi

  SEC_FAIL=$sec_fail
  M_SECURITY_ISSUES=$sec_fail

  if [[ $sec_fail -gt 0 ]]; then
    echo -e "\n${RED}⚠️  SECURITY: $sec_fail HIGH severity issues${NC}"
  else
    echo -e "\n${GREEN}✓ Security scan passed${NC}"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 2.5: SQUAD AGNOSTICISM CHECK (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_squad_agnosticism() {
  log_section "PHASE 2.5: Squad Agnosticism Check"
  local agn_violations=0
  local agn_details=""
  local agn_exclude_args=(
    --exclude-dir=.git
    --exclude-dir=node_modules
    --exclude-dir=tests
    --exclude-dir=docs
    --exclude-dir=data
    --exclude-dir=scripts
    --exclude-dir=lib
    --exclude-dir=server
  )

  if [[ ! -f "$SQUAD_DIR/config.yaml" ]]; then
    log_info "No config.yaml, skipping agnosticism check"
    return 0
  fi

  while IFS= read -r excluded_dir; do
    [[ -n "$excluded_dir" ]] || continue
    agn_exclude_args+=("--exclude-dir=$excluded_dir")
  done < <(collect_agnosticism_excluded_dirs)

  # 1. Check for hardcoded URLs (excluding generic/platform/documentation URLs)
  # Scans config, agents, tasks, workflows, templates, checklists (core squad files)
  # Excludes: docs/ (historical handoffs), data/ (operational logs), scripts/ (implementation)
  local url_hits=""
  url_hits=$(grep -rInE \
    --include="*.yaml" --include="*.yml" --include="*.md" \
    "${agn_exclude_args[@]}" \
    "https?://[^ )'\">{}\`]+" "$SQUAD_DIR" \
    2>/dev/null \
    | grep -vE "(github\.com|npmjs\.com|docs\.|documentation|wikipedia|example\.com|localhost|127\.0\.0\.1|schema\.org|json-schema|yaml\.org|commonmark|youtube\.com|youtu\.be|cloud\.google\.com|amazon\.com|goodreads\.com|ted\.com|supabase\.co|supabase\.com|googleapis\.com|stackoverflow\.com|medium\.com|apple\.com|spotify\.com|oprah\.com|podcasts\.|\"https://\.\.\.\"|lewishowes\.com|\[X\].*https://)" \
    || true)
  if [[ -n "$url_hits" ]]; then
    local url_count
    url_count=$(echo "$url_hits" | wc -l | tr -d ' ')
    log_warn "AGN-001: Found $url_count potentially business-specific URLs"
    agn_violations=$((agn_violations + url_count))
    agn_details="${agn_details}AGN-001: $url_count specific URLs found\n"
    if [[ "$VERBOSE" == "true" ]]; then
      echo "$url_hits" | head -5
    fi
  else
    log_pass "AGN-001: No business-specific URLs found"
  fi

  # 2. Check for personal names in team section of config.yaml
  local team_names=""
  team_names=$(awk '
    BEGIN { in_team=0 }
    /^team:/ { in_team=1; next }
    in_team && /^[^[:space:]]/ { in_team=0 }
    in_team && /owner:|reviewer|lead:/ {
      gsub(/^[[:space:]]*[a-z_]+:[[:space:]]*/, "", $0)
      gsub(/["'\'']/, "", $0)
      gsub(/[[:space:]]+$/, "", $0)
      if ($0 != "" && $0 !~ /^@/ && $0 !~ /^(TBD|tbd|none|N\/A)$/) print $0
    }
  ' "$SQUAD_DIR/config.yaml" 2>/dev/null || true)
  if [[ -n "$team_names" ]]; then
    local name_count
    name_count=$(echo "$team_names" | wc -l | tr -d ' ')
    log_warn "AGN-002: Found $name_count personal names in team section (squads should be agnostic)"
    agn_violations=$((agn_violations + name_count))
    agn_details="${agn_details}AGN-002: $name_count personal names in team section\n"
  else
    log_pass "AGN-002: No personal names in team section"
  fi

  # 3. Check for hardcoded project/account IDs
  local id_hits=""
  id_hits=$(grep -rInE \
    --include="*.yaml" --include="*.yml" \
    "${agn_exclude_args[@]}" \
    "(project_id|account_id|client_id|tenant_id)[[:space:]]*:[[:space:]]*['\"]?[A-Za-z0-9_-]{6,}" "$SQUAD_DIR" \
    2>/dev/null \
    | grep -vE "(\{\{|\\\$\{|<|placeholder|example|YOUR_)" \
    || true)
  if [[ -n "$id_hits" ]]; then
    local id_count
    id_count=$(echo "$id_hits" | wc -l | tr -d ' ')
    log_warn "AGN-003: Found $id_count hardcoded project/account IDs"
    agn_violations=$((agn_violations + id_count))
    agn_details="${agn_details}AGN-003: $id_count hardcoded IDs\n"
  else
    log_pass "AGN-003: No hardcoded project/account IDs"
  fi

  # 4. Check for business-specific pricing, product names in non-data files
  local biz_hits=""
  biz_hits=$(grep -rInE \
    --include="*.yaml" --include="*.yml" --include="*.md" \
    "${agn_exclude_args[@]}" \
    --exclude-dir=examples --exclude-dir=sources --exclude-dir=data \
    "(R\\\$[[:space:]]*[0-9]+|US\\\$[[:space:]]*[0-9]+|\\$[0-9]{2,}[.,][0-9]{2})" "$SQUAD_DIR" \
    2>/dev/null \
    | grep -vE "(example|template|placeholder|mock|sample|docs/)" \
    || true)
  if [[ -n "$biz_hits" ]]; then
    local biz_count
    biz_count=$(echo "$biz_hits" | wc -l | tr -d ' ')
    log_warn "AGN-004: Found $biz_count potential business-specific pricing references"
    agn_violations=$((agn_violations + biz_count))
    agn_details="${agn_details}AGN-004: $biz_count pricing references\n"
  else
    log_pass "AGN-004: No business-specific pricing"
  fi

  M_AGNOSTICISM_VIOLATIONS=$agn_violations
  M_AGNOSTICISM_DETAILS="$agn_details"

  if [[ $agn_violations -gt 0 ]]; then
    echo -e "\n${YELLOW}⚠️  AGNOSTICISM: $agn_violations violations found${NC}"
  else
    echo -e "\n${GREEN}✓ Squad agnosticism check passed${NC}"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 3: CROSS-REFERENCE (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_cross_references() {
  log_section "PHASE 3: Cross-Reference Validation (Bash)"
  local xref_fail=0

  log_subsection "3.1 Handoff Targets"

  if [[ -d "$SQUAD_DIR/agents" ]]; then
    for agent_file in "$SQUAD_DIR/agents"/*.md; do
      [[ -f "$agent_file" ]] || continue
      local handoffs=$(grep -oE "handoff_to:[[:space:]]*@?[a-z0-9_-]+" "$agent_file" 2>/dev/null | sed 's/handoff_to:[[:space:]]*@*//' || true)
      for handoff in $handoffs; do
        if ! asset_exists "agents" "${handoff}.md"; then
          log_fail "XREF-001: Handoff target not found: $handoff (in $(basename "$agent_file"))"
          xref_fail=$((xref_fail + 1))
        else
          log_pass "XREF-001: Handoff valid: $handoff"
        fi
      done
    done
  fi

  log_subsection "3.2 Task References"
  # Check structured task dependencies in agent files
  if [[ -d "$SQUAD_DIR/agents" ]]; then
    for agent_file in "$SQUAD_DIR/agents"/*.md; do
      [[ -f "$agent_file" ]] || continue
      local in_tasks=0
      while IFS= read -r line; do
        if echo "$line" | grep -qE "^[[:space:]]*tasks:[[:space:]]*$"; then
          in_tasks=1
          continue
        fi
        if echo "$line" | grep -qE "^[[:space:]]*(templates|checklists|data|workflows|agents):[[:space:]]*$"; then
          in_tasks=0
          continue
        fi
        if [[ "$in_tasks" -eq 1 ]]; then
          if [[ "$line" =~ ^[[:space:]]*-[[:space:]]+([a-z0-9_-]+)\.md ]]; then
            local task_ref="${BASH_REMATCH[1]}"
            if [[ -n "$CONFIG_TASK_IDS" ]]; then
              if ! echo "$CONFIG_TASK_IDS" | grep -qx "$task_ref"; then
                continue
              fi
            fi
            if asset_exists "tasks" "${task_ref}.md"; then
              log_pass "XREF-002: Task exists: $task_ref"
            else
              log_warn "XREF-002: Task dependency reference not found: $task_ref (in $(basename "$agent_file"))"
            fi
          fi
        fi
      done < "$agent_file"
    done
  fi

  XREF_FAIL=$xref_fail
  M_XREF_ISSUES=$xref_fail

  if [[ $xref_fail -gt 0 ]]; then
    echo -e "\n${RED}⚠️  CROSS-REF: $xref_fail broken references${NC}"
  else
    echo -e "\n${GREEN}✓ Cross-references valid${NC}"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 3.5: WORKFLOW CONTRACTS (Deterministic - CI parity)
# ═══════════════════════════════════════════════════════════════════════════════

check_workflow_contracts() {
  log_section "PHASE 3.5: Workflow Contract Validation (CI parity)"
  local workflow_fail=0

  if [[ ! -d "$SQUAD_DIR/workflows" ]]; then
    log_info "No workflows/ directory, skipping workflow contract validation"
    WF_CONTRACT_FAIL=0
    M_WORKFLOW_CONTRACT_FILES=0
    M_WORKFLOW_CONTRACT_ERRORS=0
    M_WORKFLOW_CONTRACT_WARNINGS=0
    return 0
  fi

  local workflow_files=0
  workflow_files=$(find "$SQUAD_DIR/workflows" -maxdepth 1 -type f \( -name "*.yaml" -o -name "*.yml" \) 2>/dev/null | wc -l | tr -d ' ')

  if [[ "$workflow_files" -eq 0 ]]; then
    log_info "No workflow files found in workflows/, skipping workflow contract validation"
    WF_CONTRACT_FAIL=0
    M_WORKFLOW_CONTRACT_FILES=0
    M_WORKFLOW_CONTRACT_ERRORS=0
    M_WORKFLOW_CONTRACT_WARNINGS=0
    return 0
  fi

  local contract_output=""
  if contract_output=$(node "$WORKFLOW_CONTRACT_VALIDATOR" --squads "$SQUAD_NAME" --strict --fail-on-warnings --json 2>&1); then
    :
  else
    workflow_fail=1
  fi

  local files_checked=0
  local errors_count=0
  local warnings_count=0
  local invalid_files_count=0
  while IFS=$'\t' read -r key value; do
    case "$key" in
      files_checked) files_checked="$value" ;;
      errors) errors_count="$value" ;;
      warnings) warnings_count="$value" ;;
      invalid_files) invalid_files_count="$value" ;;
    esac
  done < <(printf "%s" "$contract_output" | parse_workflow_contract_totals)

  M_WORKFLOW_CONTRACT_FILES="$files_checked"
  M_WORKFLOW_CONTRACT_ERRORS="$errors_count"
  M_WORKFLOW_CONTRACT_WARNINGS="$warnings_count"

  if [[ "$workflow_fail" -eq 0 ]]; then
    log_pass "WF-001: Workflow contracts valid (files=$files_checked, errors=$errors_count, warnings=$warnings_count)"
  else
    log_fail "WF-001: Workflow contract validation failed (files=$files_checked, errors=$errors_count, warnings=$warnings_count, invalid=$invalid_files_count)"
    if [[ "$VERBOSE" == "true" ]]; then
      echo "$contract_output"
    fi
  fi

  WF_CONTRACT_FAIL="$workflow_fail"
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 4: SQUAD TYPE DETECTION (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

detect_squad_type() {
  log_section "PHASE 4: Squad Type Detection (Bash)"

  local type="general"
  local confidence=5

  # Check for Expert indicators
  local has_voice_dna=$(find "$SQUAD_DIR" -name "*voice*" -o -name "*dna*" 2>/dev/null | wc -l | tr -d ' ')
  local has_clone=$(grep -ril "clone\|emulat\|mind\|persona" "$SQUAD_DIR/agents" 2>/dev/null | wc -l | tr -d ' ')

  # Check for Pipeline indicators
  local has_workflow=$(find "$SQUAD_DIR" -path "*/workflows/*.yaml" 2>/dev/null | wc -l | tr -d ' ')
  local has_phases=$(grep -ril "phase\|stage\|step" "$SQUAD_DIR/tasks" 2>/dev/null | wc -l | tr -d ' ')

  # Calculate task ratio
  local agent_count=${M_AGENT_COUNT:-1}
  [[ $agent_count -eq 0 ]] && agent_count=1
  local task_ratio=$((M_TASK_COUNT / agent_count))

  # Check for Hybrid indicators
  local has_human_exec=$(grep -ril "human\|manual\|executor" "$SQUAD_DIR" 2>/dev/null | wc -l | tr -d ' ')

  # Scoring
  local expert_score=0
  local pipeline_score=0
  local hybrid_score=0

  [[ $has_voice_dna -gt 0 ]] && expert_score=$((expert_score + 3))
  [[ $has_clone -gt 2 ]] && expert_score=$((expert_score + 2))

  [[ $has_workflow -gt 0 ]] && pipeline_score=$((pipeline_score + 3))
  [[ $has_phases -gt 3 ]] && pipeline_score=$((pipeline_score + 2))
  [[ $task_ratio -gt 3 ]] && pipeline_score=$((pipeline_score + 2))

  [[ $has_human_exec -gt 2 ]] && hybrid_score=$((hybrid_score + 3))

  # Determine type
  if [[ $expert_score -ge 4 ]]; then
    type="expert"
    confidence=$expert_score
  elif [[ $pipeline_score -ge 4 ]]; then
    type="pipeline"
    confidence=$pipeline_score
  elif [[ $hybrid_score -ge 3 ]]; then
    type="hybrid"
    confidence=$hybrid_score
  fi

  M_SQUAD_TYPE="$type"
  M_TYPE_CONFIDENCE="$confidence"

  log_info "Detected type: $type (confidence: $confidence)"
  log_info "Expert signals: voice_dna=$has_voice_dna, clone_refs=$has_clone"
  log_info "Pipeline signals: workflows=$has_workflow, phases=$has_phases, task_ratio=$task_ratio"
  log_info "Hybrid signals: human_exec=$has_human_exec"

  echo -e "\n${CYAN}Squad Type: ${BOLD}$type${NC} (confidence: $confidence/7)"
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 3.7: OUTPUT PATH GOVERNANCE (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_output_path_governance() {
  log_section "PHASE 3.7: Output Path Governance (Bash)"
  # ═══════════════════════════════════════════════════════════════════════════
  # Applies Pedro Valerio heuristics:
  #   PV004: "Se o executor CONSEGUE fazer errado, processo esta errado"
  #          → BLOCK contradictions, dont just warn
  #   PV008: "Automacao sem guardrails nao pode rodar"
  #          → 3 guardrails: declaration check, signal check, integration check
  #   Hierarchy: Bloquear > Alertar > Documentar
  #
  # 3 checks, escalating severity:
  #   OPG-001 (BLOCKING): Task declares canonical_workspace but path is .aiox/squad-runtime/
  #   OPG-002 (BLOCKING): Squad declares workspace integration but 0 tasks use workspace/
  #   OPG-003 (WARNING):  Task has HIGH-VALUE signals + runtime path (heuristic)
  # ═══════════════════════════════════════════════════════════════════════════
  local opg_fail=0
  local opg_warnings=0

  if [[ ! -d "$SQUAD_DIR/tasks" ]]; then
    log_info "No tasks/ directory, skipping output path governance"
    return
  fi

  # ─── GUARDRAIL 1: Declaration contradiction (BLOCKING - PV004) ───
  # If task explicitly declares output_persistence: canonical_workspace
  # but path points to .aiox/squad-runtime/, this is a structural contradiction.
  # "Se o caminho errado e possivel, o processo esta errado."
  for task_file in "$SQUAD_DIR/tasks"/*.md; do
    [[ -f "$task_file" ]] || continue
    local task_name=$(basename "$task_file")

    # Check if task declares canonical_workspace
    local declares_canonical=$(grep -iE "output_persistence.*canonical_workspace|persistence.*canonical" "$task_file" 2>/dev/null || true)
    local has_runtime_path=$(grep -iE "path:.*\\.aiox/squad-runtime/" "$task_file" 2>/dev/null || true)

    if [[ -n "$declares_canonical" && -n "$has_runtime_path" ]]; then
      log_fail "OPG-001: Task $task_name declares output_persistence=canonical_workspace but path uses .aiox/squad-runtime/. PV004 VETO: structural contradiction. Fix path to workspace/businesses/{business}/"
      opg_fail=$((opg_fail + 1))
    fi

    # Inverse check: declares transient but path is workspace/
    local declares_transient=$(grep -iE "output_persistence.*transient_output|persistence.*transient" "$task_file" 2>/dev/null || true)
    local has_workspace_path=$(grep -iE "path:.*workspace/businesses" "$task_file" 2>/dev/null || true)

    if [[ -n "$declares_transient" && -n "$has_workspace_path" ]]; then
      log_warn "OPG-001b: Task $task_name declares output_persistence=transient_output but path uses workspace/. Verify classification."
      opg_warnings=$((opg_warnings + 1))
    fi
  done

  # ─── GUARDRAIL 2: Integration level contradiction (BLOCKING - PV004) ───
  # If config.yaml declares controlled_runtime_consumer or workspace_first
  # but ALL tasks output to .aiox/squad-runtime/ and ZERO to workspace/, the squad
  # contradicts its own declared integration level.
  if [[ -f "$SQUAD_DIR/config.yaml" ]]; then
    local ws_level=$(grep -E "^\s+level:" "$SQUAD_DIR/config.yaml" 2>/dev/null | head -1 | sed 's/.*level:[[:space:]]*//' | tr -d '"' || true)
    if [[ "$ws_level" == "controlled_runtime_consumer" || "$ws_level" == "workspace_first" ]]; then
      local tasks_using_workspace=$(grep -rlE "path:.*workspace/" "$SQUAD_DIR/tasks/" 2>/dev/null | wc -l | tr -d ' ')
      local tasks_using_runtime=$(grep -rlE "path:.*\\.aiox/squad-runtime/" "$SQUAD_DIR/tasks/" 2>/dev/null | wc -l | tr -d ' ')

      if [[ "$tasks_using_runtime" -gt 0 && "$tasks_using_workspace" -eq 0 ]]; then
        log_fail "OPG-002: Squad declares workspace_integration.level=$ws_level but ALL task outputs ($tasks_using_runtime) go to .aiox/squad-runtime/, ZERO to workspace/. PV004 VETO: integration level contradicts task paths."
        opg_fail=$((opg_fail + 1))
      fi
    fi
  fi

  # ─── GUARDRAIL 3: HIGH-VALUE signal heuristic (WARNING) ───
  # Heuristic fallback for tasks that dont declare output_persistence.
  # If task outputs to .aiox/squad-runtime/ AND contains HIGH-VALUE signal words,
  # flag for human review. This is Alertar (not Bloquear) because
  # the signal is probabilistic, not deterministic.
  local high_value_signals="score|maturity|health|onboarding|analytics|kpi|scorecard|diagnosis|assessment|strategy|retention|churn|nps|journey|activation"

  for task_file in "$SQUAD_DIR/tasks"/*.md; do
    [[ -f "$task_file" ]] || continue
    local task_name=$(basename "$task_file")

    local has_runtime_path=$(grep -iE "path:.*\\.aiox/squad-runtime/" "$task_file" 2>/dev/null || true)
    if [[ -z "$has_runtime_path" ]]; then
      continue
    fi

    # Skip if already caught by GUARDRAIL 1 (has explicit declaration)
    local has_declaration=$(grep -iE "output_persistence" "$task_file" 2>/dev/null || true)
    if [[ -n "$has_declaration" ]]; then
      continue
    fi

    # No declaration, check signal words
    if grep -qiE "$high_value_signals" "$task_file" 2>/dev/null; then
      log_warn "OPG-003: Task $task_name has output path in .aiox/squad-runtime/ with HIGH-VALUE signal words but no output_persistence declaration. Classify as canonical_workspace or transient_output."
      opg_warnings=$((opg_warnings + 1))
    fi
  done

  M_OPG_WARNINGS=$((opg_warnings + opg_fail))

  if [[ $opg_fail -gt 0 ]]; then
    echo -e "\n${RED}✗ Output Path Governance: $opg_fail BLOCKING violations, $opg_warnings warnings${NC}"
  elif [[ $opg_warnings -gt 0 ]]; then
    echo -e "\n${YELLOW}⚠️  Output Path Governance: $opg_warnings warnings (no blocking)${NC}"
  else
    echo -e "\n${GREEN}✓ Output path governance passed${NC}"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 5: PRODUCTION VALIDATION (Deterministic - Bash)
# ═══════════════════════════════════════════════════════════════════════════════

check_production() {
  log_section "PHASE 5: Production Validation (Bash)"
  local prod_score=0
  local manifest_type=""
  local workspace_level=""
  local runtime_evidence_optional=false
  local contract_test_files=0
  local operational_story_files=0

  manifest_type=$(extract_config_scalar "type")
  workspace_level=$(extract_workspace_integration_level)
  contract_test_files=$(count_contract_test_files 2>/dev/null || echo 0)
  operational_story_files=$(count_operational_story_files 2>/dev/null || echo 0)

  if [[ "$manifest_type" == "specialist" && "$workspace_level" == "none" ]]; then
    runtime_evidence_optional=true
  fi

  log_subsection "5.1 Runtime Evidence"
  # Canonical runtime evidence, when applicable, must live in .aiox/squad-runtime
  local has_runtime_evidence=false
  local runtime_root="${AIOX_RUNTIME_ROOT:-./.aiox/squad-runtime}"
  if [ -d "$runtime_root" ]; then
    local squad_runtime_dir
    squad_runtime_dir=$(find "$runtime_root" -maxdepth 3 -type d -name "$SQUAD_NAME" 2>/dev/null | head -1)
    if [ -n "$squad_runtime_dir" ] && [ -d "$squad_runtime_dir" ]; then
      local output_count
      output_count=$(find "$squad_runtime_dir" -type f 2>/dev/null | wc -l | tr -d ' ')
      if [ "$output_count" -gt 0 ]; then
        log_pass "Found runtime evidence in .aiox/squad-runtime ($output_count files)"
        has_runtime_evidence=true
        prod_score=$((prod_score + 2))
      else
        log_warn "Runtime directory exists but has no files: $squad_runtime_dir"
      fi
    fi
  fi

  if [ "$has_runtime_evidence" = false ]; then
    if [ "$runtime_evidence_optional" = true ]; then
      log_info "Runtime evidence optional for type='$manifest_type' with workspace_integration.level='$workspace_level'"
    else
      log_warn "No runtime evidence found in .aiox/squad-runtime for squad '$SQUAD_NAME'"
    fi
  fi

  log_subsection "5.2 Tested Flag"
  # Check for tested: true in config.yaml or infer from runtime, declared outputs,
  # or contract-test evidence for non-runtime specialist squads.
  if grep -qE "^tested:[[:space:]]*(true|yes)" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
    log_pass "config.yaml has tested: true"
    prod_score=$((prod_score + 1))
  else
    local inferred_tested=false
    local declared_output_files=0

    if [ "$has_runtime_evidence" = true ]; then
      log_pass "config.yaml missing tested flag, but runtime evidence is sufficient to infer tested status"
      inferred_tested=true
    else
      declared_output_files=$(count_declared_output_files 2>/dev/null || echo 0)
      if [[ "$declared_output_files" -gt 0 ]]; then
        log_pass "config.yaml missing tested flag, but declared output path contains evidence ($declared_output_files files)"
        inferred_tested=true
      elif [[ "$contract_test_files" -gt 0 ]]; then
        log_pass "config.yaml missing tested flag, but contract/runtime test coverage exists ($contract_test_files files)"
        inferred_tested=true
      fi
    fi

    if [ "$inferred_tested" = true ]; then
      prod_score=$((prod_score + 1))
    else
      log_warn "config.yaml missing 'tested: true' flag and no runtime, output, or test evidence was found to infer it"
    fi
  fi

  log_subsection "5.3 Usage Evidence"
  # YOLO evidence is only required when config declares settings.activation.yolo_required=true.
  local yolo_required=false
  if grep -qE '^[[:space:]]*yolo_required:[[:space:]]*(true|yes|1)[[:space:]]*$' "$SQUAD_DIR/config.yaml" 2>/dev/null; then
    yolo_required=true
  fi

  if [ "$yolo_required" = true ]; then
    local state_files
    state_files=$(find "$SQUAD_DIR" -name "*-state.json" -o -name "progress.txt" -o -name "handoff.md" 2>/dev/null | wc -l | tr -d ' ')
    if [ "$state_files" -gt 0 ]; then
      # Verify it's real usage, not just template files
      local real_state
      real_state=$(find "$SQUAD_DIR" -name "*-state.json" -exec grep -l '"status"' {} \; 2>/dev/null | wc -l | tr -d ' ')
      if [ "$real_state" -gt 0 ]; then
        log_pass "Found $real_state state files with execution history (YOLO mode required)"
        prod_score=$((prod_score + 1))
      else
        log_warn "YOLO required but state files found appear to be templates"
      fi
    else
      log_warn "YOLO required but no state files found (add *-state.json/progress evidence)"
    fi
  else
    log_info "YOLO mode evidence not required (settings.activation.yolo_required=false)"
  fi

  # Check for user feedback or validation reports
  local feedback_files=$(find "$SQUAD_DIR" -name "*feedback*" -o -name "*validation-report*" -o -name "*qa-report*" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$feedback_files" -gt 0 ]; then
    log_pass "Found $feedback_files feedback/validation files"
    prod_score=$((prod_score + 1))
  else
    local output_usage_files=0
    output_usage_files=$(count_usage_evidence_output_files 2>/dev/null || echo 0)
    if [ "$output_usage_files" -gt 0 ]; then
      log_pass "Found $output_usage_files canonical output artifact(s) in declared output root"
      prod_score=$((prod_score + 1))
    fi
  fi

  log_subsection "5.4 Examples & Operational Evidence"
  # Check for operational examples in docs, templates, or validation stories.
  local has_examples=false
  if [ -d "$SQUAD_DIR/examples" ] || [ -d "$SQUAD_DIR/samples" ]; then
    log_pass "examples/ or samples/ directory exists"
    has_examples=true
    prod_score=$((prod_score + 1))
  fi

  # Check for output_examples in agents
  local output_examples=$(grep -rl "output_examples\|example_output\|sample_output" "$SQUAD_DIR/agents" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$output_examples" -gt 0 ]; then
    log_pass "Found output examples in $output_examples agent files"
    if [ "$has_examples" = false ]; then
      prod_score=$((prod_score + 1))
    fi
    has_examples=true
  fi

  if [ "$has_examples" = false ] && [ "$operational_story_files" -gt 0 ]; then
    log_pass "Found $operational_story_files operational docs/stories for squad '$SQUAD_NAME'"
    has_examples=true
    prod_score=$((prod_score + 1))
  fi

  if [ "$has_examples" = false ]; then
    log_warn "No operational examples found (examples/, samples/, output_examples, or relevant docs/stories)"
  fi

  # Cap at max
  if [ $prod_score -gt $PROD_MAX ]; then
    prod_score=$PROD_MAX
  fi

  PROD_SCORE=$prod_score
  M_PROD_SCORE=$prod_score

  echo ""
  if [ $prod_score -eq 0 ]; then
    echo -e "${RED}⚠️  PRODUCTION: 0/$PROD_MAX - No evidence of real usage${NC}"
    echo -e "${YELLOW}   Max possible score without production evidence: 5/10${NC}"
  elif [ $prod_score -lt 3 ]; then
    echo -e "${YELLOW}⚠️  PRODUCTION: $prod_score/$PROD_MAX - Limited production evidence${NC}"
  else
    echo -e "${GREEN}✓ Production validation: $prod_score/$PROD_MAX${NC}"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 6: QUALITY ANALYSIS (Claude CLI)
# ═══════════════════════════════════════════════════════════════════════════════

analyze_with_claude() {
  log_section "$(t phase6_title)"

  if [[ "$QUICK_MODE" == "true" ]]; then
    echo -e "${YELLOW}$(t phase6_skip)${NC}"
    M_QUALITY_SCORE="N/A"
    return 0
  fi

  echo -e "${MAGENTA}$(fmt_t phase6_running "$MODEL_QUALITY")${NC}"

  # Read FULL config.yaml (highest priority)
  local config_content=""
  [[ -f "$SQUAD_DIR/config.yaml" ]] && config_content=$(cat "$SQUAD_DIR/config.yaml" 2>/dev/null || true)

  # Read FULL entry agent
  local agent_content=""
  local sample_agent=""
  if [[ -n "${ENTRY_AGENT:-}" ]]; then
    if [[ -f "$SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      sample_agent="$SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    elif [[ -n "$INHERITED_SQUAD_DIR" ]] && [[ -f "$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md" ]]; then
      sample_agent="$INHERITED_SQUAD_DIR/agents/${ENTRY_AGENT}.md"
    fi
  fi
  if [[ -z "$sample_agent" ]]; then
    sample_agent=$(find "$SQUAD_DIR/agents" -name "*.md" 2>/dev/null | head -1)
  fi
  [[ -f "$sample_agent" ]] && agent_content=$(cat "$sample_agent" 2>/dev/null || true)

  # Read FULL first workflow
  local workflow_content=""
  local sample_workflow
  sample_workflow=$(find "$SQUAD_DIR/workflows" -name "*.yaml" -o -name "*.yml" 2>/dev/null | head -1)
  [[ -f "$sample_workflow" ]] && workflow_content=$(cat "$sample_workflow" 2>/dev/null || true)

  # Truncation safety: if config + agent > 15000 chars, truncate agent (config has priority)
  local config_len=${#config_content}
  local agent_len=${#agent_content}
  local workflow_len=${#workflow_content}
  local max_content=15000

  if [[ $((config_len + agent_len + workflow_len)) -gt $max_content ]]; then
    # Config always full; split remaining between agent and workflow
    local remaining=$((max_content - config_len))
    if [[ $remaining -lt 1000 ]]; then
      remaining=1000
    fi
    local agent_max=$((remaining * 70 / 100))
    local wf_max=$((remaining * 30 / 100))
    if [[ $agent_len -gt $agent_max ]]; then
      agent_content="${agent_content:0:$agent_max}

... [TRUNCATED at $agent_max chars — full file: $(basename "$sample_agent")] ..."
    fi
    if [[ $workflow_len -gt $wf_max ]]; then
      workflow_content="${workflow_content:0:$wf_max}

... [TRUNCATED at $wf_max chars] ..."
    fi
  fi

  # Build findings summary from previous phases
  local findings_summary="## Previous Phase Findings

### Structure (Phase 1)
- TIER1 failures: $TIER1_FAIL
- Mandatory structural checks: $M_STRUCT_COMPLETENESS_PASS/$M_STRUCT_COMPLETENESS_TOTAL
- Contextual lifecycle checks: $M_CONTEXTUAL_LIFECYCLE_PASS/$M_CONTEXTUAL_LIFECYCLE_TOTAL (warnings: $M_CONTEXTUAL_LIFECYCLE_WARNINGS)
- Agent quality gaps (entry agent): $M_AGENT_QUALITY_GAPS/5
- Version consistent: $M_VERSION_CONSISTENT${M_VERSION_DETAILS:+ ($M_VERSION_DETAILS)}

### Security (Phase 2)
- Security issues found: $SEC_FAIL
$(if [[ -n "$BLOCKING_ISSUES" ]]; then echo "- Blocking issues detail:"; echo -e "$BLOCKING_ISSUES" | grep -E "SEC-" | while read -r line; do [[ -n "$line" ]] && echo "  - $line"; done; fi)

### Squad Agnosticism (Phase 2.5)
- Agnosticism violations: $M_AGNOSTICISM_VIOLATIONS
$(if [[ -n "$M_AGNOSTICISM_DETAILS" ]]; then echo -e "$M_AGNOSTICISM_DETAILS" | while read -r line; do [[ -n "$line" ]] && echo "  - $line"; done; fi)

### Cross-References (Phase 3)
- Broken references: $XREF_FAIL

### Workflow Contracts (Phase 3.5)
- Files checked: $M_WORKFLOW_CONTRACT_FILES
- Errors: $M_WORKFLOW_CONTRACT_ERRORS
- Warnings: $M_WORKFLOW_CONTRACT_WARNINGS

### Production (Phase 5)
- Production score: $PROD_SCORE/$PROD_MAX"

  # Build dimensional analysis prompt
  local ANALYSIS_PROMPT="You are a senior squad quality auditor for the AIOX framework. Perform a deep dimensional analysis.

IMPORTANT: Respond with ONLY valid JSON. No markdown, no explanation, no code fences.
IMPORTANT: Keep the JSON keys exactly as requested below.
IMPORTANT: Write every human-readable value in ${ANALYSIS_LANGUAGE_NAME}. This includes diagnosis, recommendation, detail, strengths, improvements, and priority_fixes.
IMPORTANT: Do NOT localize the response to the end-user language. This JSON is the canonical internal analysis artifact.

## Squad: $SQUAD_NAME
Type: $M_SQUAD_TYPE (confidence: $M_TYPE_CONFIDENCE)
Agents: $M_AGENT_COUNT | Tasks: $M_TASK_COUNT | Checklists: $M_CHECKLIST_COUNT | Lines: $M_TOTAL_LINES

$findings_summary

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

## Historical Calibration (prior run scores — justify if you diverge significantly)
$(_get_historical_scores)

## Analysis Instructions

Score each dimension 0-10. Be STRICT — a score of 7+ means production-ready quality.

For security findings (SEC-*), evaluate if they are FALSE_POSITIVE (e.g., book excerpts mentioning \"secret\", example patterns) or REAL threats.

For squad agnosticism, check if the squad contains business-specific data (company names, real pricing, personal names, specific product references) that should live in workspace/ instead.

## Required JSON Response:
{
  \"blocking_issues_analysis\": [
    {\"id\": \"SEC-002\", \"verdict\": \"FALSE_POSITIVE or REAL\", \"diagnosis\": \"why\", \"recommendation\": \"what to do\"}
  ],
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

  # Run Claude — write prompt to temp file to avoid ARG_MAX / printf truncation
  local claude_output
  log_info "$(fmt_t phase6_prompt_written "${#ANALYSIS_PROMPT}")"

  if claude_output=$(run_llm_prompt_with_replan "$MODEL_QUALITY" "$ANALYSIS_PROMPT" "${PROGRESS_LOG:-/dev/null}" "validate" 2>&1); then
    local json_result report_json_result
    json_result=$(printf "%s" "$claude_output" | extract_first_json_object)

    # Store raw JSON for report generation
    CLAUDE_RAW_JSON="$json_result"
    report_json_result=$(localize_review_json_for_report "$json_result")
    CLAUDE_REPORT_JSON="$report_json_result"

    # Extract dimensional scores via python for robustness
    # Returns empty string for missing dimensions (triggers deterministic fallback)
    local parsed_scores
    parsed_scores=$(extract_review_fields "$json_result")

    # Parse dimensional scores
    while IFS=$'\t' read -r key value; do
      case "$key" in
        structural_completeness) CLAUDE_STRUCTURAL_COMPLETENESS="$value" ;;
        security_audit) CLAUDE_SECURITY_AUDIT="$value" ;;
        workflow_analysis) CLAUDE_WORKFLOW_ANALYSIS="$value" ;;
        agent_quality) CLAUDE_AGENT_QUALITY="$value" ;;
        squad_agnosticism) CLAUDE_SQUAD_AGNOSTICISM="$value" ;;
        config_quality) CLAUDE_CONFIG_QUALITY="$value" ;;
        production_evidence) CLAUDE_PRODUCTION_EVIDENCE="$value" ;;
        overall_score) M_QUALITY_SCORE="$value" ;;
        improvements_b64)
          M_IMPROVEMENTS=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
          M_IMPROVEMENTS_REPORT="$M_IMPROVEMENTS"
          ;;
        priority_fixes_b64)
          CLAUDE_EXEC_SUMMARY=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
          CLAUDE_EXEC_SUMMARY_REPORT="$CLAUDE_EXEC_SUMMARY"
          ;;
        false_positive_count)
          # Adjust SEC_FAIL by subtracting false positives
          local fp_count="${value%%.*}"
          if [[ "$fp_count" =~ ^[0-9]+$ ]] && [[ "$fp_count" -gt 0 ]]; then
            local adjusted=$((SEC_FAIL - fp_count))
            if [[ $adjusted -lt 0 ]]; then adjusted=0; fi
            if [[ "$REPORT_LANG_RESOLVED" == "pt-br" ]]; then
              echo -e "  ${CYAN}ℹ${NC} Segurança: $fp_count falso(s) positivo(s) detectado(s) pelo reviewer, ajustando SEC_FAIL: $SEC_FAIL → $adjusted"
            else
              echo -e "  ${CYAN}ℹ${NC} Security: $fp_count false positive(s) detected by reviewer, adjusting SEC_FAIL: $SEC_FAIL → $adjusted"
            fi
            SEC_FAIL=$adjusted
          fi
          ;;
      esac
    done <<< "$parsed_scores"

    if [[ "$LOCALIZED_REPORT_AVAILABLE" == "true" ]] && [[ "$CLAUDE_REPORT_JSON" != "$CLAUDE_RAW_JSON" ]]; then
      local localized_fields
      localized_fields=$(extract_review_fields "$CLAUDE_REPORT_JSON")
      while IFS=$'\t' read -r key value; do
        case "$key" in
          improvements_b64)
            M_IMPROVEMENTS_REPORT=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
            ;;
          priority_fixes_b64)
            CLAUDE_EXEC_SUMMARY_REPORT=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "")' 2>/dev/null || printf '%s' "$value")
            ;;
        esac
      done <<< "$localized_fields"
    fi

    if [[ "$VERBOSE" == "true" ]]; then
      echo -e "\n${CYAN}$(t phase6_result)${NC}"
      echo -e "  $(fmt_t phase6_language_state "$ANALYSIS_LANG" "$REPORT_LANG_RESOLVED")"
      if [[ "$REPORT_LANG_RESOLVED" != "$ANALYSIS_LANG" ]] && [[ "$LOCALIZED_REPORT_AVAILABLE" != "true" ]]; then
        echo -e "  ${YELLOW}$(t phase6_localization_fallback)${NC}"
      fi
      echo "$CLAUDE_REPORT_JSON" | python3 -m json.tool 2>/dev/null || echo "$CLAUDE_REPORT_JSON"
    fi

    if ! is_numeric_score "${M_QUALITY_SCORE:-}"; then
      M_QUALITY_SCORE="N/A"
      if [[ "$REPORT_LANG_RESOLVED" == "pt-br" ]]; then
        echo -e "${YELLOW}⚠️  saída do reviewer sem overall_score parseável; usando fallback determinístico${NC}"
      else
        echo -e "${YELLOW}⚠️  reviewer output missing parseable overall_score; using deterministic fallback${NC}"
      fi
    else
      M_QUALITY_SCORE=$(clamp_score_0_10 "$M_QUALITY_SCORE")
    fi

    echo -e "\n${GREEN}✓ $(t phase6_complete)${NC}"
    if [[ "$REPORT_LANG_RESOLVED" == "pt-br" ]]; then
      echo -e "  Pontuações dimensionais:"
      [[ -n "$CLAUDE_STRUCTURAL_COMPLETENESS" ]] && echo -e "    $(dimension_label structural_completeness): ${BOLD}${CLAUDE_STRUCTURAL_COMPLETENESS}/10${NC}"
      [[ -n "$CLAUDE_SECURITY_AUDIT" ]] && echo -e "    Auditoria de Segurança:   ${BOLD}${CLAUDE_SECURITY_AUDIT}/10${NC}"
      [[ -n "$CLAUDE_WORKFLOW_ANALYSIS" ]] && echo -e "    Análise de Workflow:      ${BOLD}${CLAUDE_WORKFLOW_ANALYSIS}/10${NC}"
      [[ -n "$CLAUDE_AGENT_QUALITY" ]] && echo -e "    $(dimension_label agent_quality):        ${BOLD}${CLAUDE_AGENT_QUALITY}/10${NC}"
      [[ -n "$CLAUDE_SQUAD_AGNOSTICISM" ]] && echo -e "    $(dimension_label squad_agnosticism):    ${BOLD}${CLAUDE_SQUAD_AGNOSTICISM}/10${NC}"
      [[ -n "$CLAUDE_CONFIG_QUALITY" ]] && echo -e "    $(dimension_label config_quality):    ${BOLD}${CLAUDE_CONFIG_QUALITY}/10${NC}"
      [[ -n "$CLAUDE_PRODUCTION_EVIDENCE" ]] && echo -e "    $(dimension_label production_evidence): ${BOLD}${CLAUDE_PRODUCTION_EVIDENCE}/10${NC}"
      echo -e "    Geral:                      ${BOLD}${M_QUALITY_SCORE}/10${NC}"
    else
      echo -e "  Dimensional scores:"
      [[ -n "$CLAUDE_STRUCTURAL_COMPLETENESS" ]] && echo -e "    $(dimension_label structural_completeness): ${BOLD}${CLAUDE_STRUCTURAL_COMPLETENESS}/10${NC}"
      [[ -n "$CLAUDE_SECURITY_AUDIT" ]] && echo -e "    Security Audit:          ${BOLD}${CLAUDE_SECURITY_AUDIT}/10${NC}"
      [[ -n "$CLAUDE_WORKFLOW_ANALYSIS" ]] && echo -e "    Workflow Analysis:       ${BOLD}${CLAUDE_WORKFLOW_ANALYSIS}/10${NC}"
      [[ -n "$CLAUDE_AGENT_QUALITY" ]] && echo -e "    $(dimension_label agent_quality):           ${BOLD}${CLAUDE_AGENT_QUALITY}/10${NC}"
      [[ -n "$CLAUDE_SQUAD_AGNOSTICISM" ]] && echo -e "    $(dimension_label squad_agnosticism):       ${BOLD}${CLAUDE_SQUAD_AGNOSTICISM}/10${NC}"
      [[ -n "$CLAUDE_CONFIG_QUALITY" ]] && echo -e "    $(dimension_label config_quality):          ${BOLD}${CLAUDE_CONFIG_QUALITY}/10${NC}"
      [[ -n "$CLAUDE_PRODUCTION_EVIDENCE" ]] && echo -e "    $(dimension_label production_evidence):     ${BOLD}${CLAUDE_PRODUCTION_EVIDENCE}/10${NC}"
      echo -e "    Overall:                 ${BOLD}${M_QUALITY_SCORE}/10${NC}"
    fi

  else
    rm -f "$prompt_file"
    echo -e "${YELLOW}⚠️  $(t phase6_failed)${NC}"
    M_QUALITY_SCORE="N/A"
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 6: FINAL SCORING & REPORT
# ═══════════════════════════════════════════════════════════════════════════════

calculate_final_score() {
  log_section "$(t phase7_title)"

  # ═══════════════════════════════════════════════════════════════════════════
  # DIMENSIONAL SCORING
  #
  # 9 dimensions with weights:
  #   HIGH   (×1.5): functionality, security, agnosticism, production
  #   MEDIUM (×1.0): workflow_contract, structural, agent_quality, config
  #   LOW    (×0.7): documentation
  #
  # Formula:
  #   weighted_avg = Σ(score_i × weight_i) / Σ(weight_i)
  #   penalty = blocking_issues × severity_multiplier
  #   final = max(0, weighted_avg - penalty)
  #   If blocking issues > 0: cap at 6/10
  #
  # Verdicts:
  #   PASS:        score >= 7.0 AND zero blocking
  #   CONDITIONAL: score >= 4.0 OR has blocking
  #   FAIL:        score < 4.0
  # ═══════════════════════════════════════════════════════════════════════════

  # --- Compute deterministic dimension scores ---

  # D1: Functionality/Pipeline (from workflow analysis or fallback)
  local d_functionality=5
  if is_numeric_score "${CLAUDE_WORKFLOW_ANALYSIS:-}"; then
    d_functionality="$CLAUDE_WORKFLOW_ANALYSIS"
    if awk -v s="$d_functionality" 'BEGIN { exit !(s < 10) }'; then
      DIM_FUNCTIONALITY_NOTE=$(fmt_t note_functionality_deep "$d_functionality")
    fi
  else
    # Deterministic fallback: based on workflow contract + type detection
    local wf_base=5
    local wf_reasons=""
    [[ "$M_WORKFLOW_CONTRACT_ERRORS" -eq 0 ]] && wf_base=$((wf_base + 2))
    [[ "$M_WORKFLOW_CONTRACT_WARNINGS" -eq 0 ]] && wf_base=$((wf_base + 1))
    [[ "$M_TYPE_CONFIDENCE" -ge 5 ]] && wf_base=$((wf_base + 1))
    [[ "$M_WORKFLOW_CONTRACT_ERRORS" -gt 0 ]] && wf_reasons="${wf_reasons}workflow_contract_errors=${M_WORKFLOW_CONTRACT_ERRORS}, "
    [[ "$M_WORKFLOW_CONTRACT_WARNINGS" -gt 0 ]] && wf_reasons="${wf_reasons}workflow_contract_warnings=${M_WORKFLOW_CONTRACT_WARNINGS}, "
    [[ "$M_TYPE_CONFIDENCE" -lt 5 ]] && wf_reasons="${wf_reasons}type_confidence=${M_TYPE_CONFIDENCE}/7, "
    [[ $wf_base -gt 10 ]] && wf_base=10
    d_functionality=$wf_base
    if awk -v s="$d_functionality" 'BEGIN { exit !(s < 10) }'; then
      if [[ -z "$wf_reasons" ]]; then
        DIM_FUNCTIONALITY_NOTE=$(t note_functionality_quick_max)
      else
        wf_reasons="${wf_reasons%, }"
        DIM_FUNCTIONALITY_NOTE=$(fmt_t note_functionality_quick_reduced "$wf_reasons")
      fi
    fi
  fi

  # D2: Security (from Claude or deterministic)
  local d_security=5
  if is_numeric_score "${CLAUDE_SECURITY_AUDIT:-}"; then
    d_security="$CLAUDE_SECURITY_AUDIT"
    if awk -v s="$d_security" 'BEGIN { exit !(s < 10) }'; then
      DIM_SECURITY_NOTE=$(fmt_t note_security_deep "$d_security")
    fi
  else
    if [[ "$SEC_FAIL" -eq 0 ]]; then
      d_security=10
    elif [[ "$SEC_FAIL" -eq 1 ]]; then
      d_security=6
    elif [[ "$SEC_FAIL" -le 3 ]]; then
      d_security=3
    else
      d_security=1
    fi
    if awk -v s="$d_security" 'BEGIN { exit !(s < 10) }'; then
      DIM_SECURITY_NOTE=$(fmt_t note_security_deterministic "$SEC_FAIL")
    fi
  fi

  # D3: Workflow Contract
  local d_workflow_contract=5
  if [[ "$M_WORKFLOW_CONTRACT_FILES" -eq 0 ]] && [[ ! -d "$SQUAD_DIR/workflows" ]]; then
    d_workflow_contract=5  # N/A, neutral
    DIM_WORKFLOW_CONTRACT_NOTE=$(t note_workflow_neutral)
  elif [[ "$WF_CONTRACT_FAIL" -eq 0 ]]; then
    d_workflow_contract=10
  else
    d_workflow_contract=$(awk -v err="$M_WORKFLOW_CONTRACT_ERRORS" -v warn="$M_WORKFLOW_CONTRACT_WARNINGS" \
      'BEGIN { s = 10 - (err * 2) - (warn * 0.5); if (s < 0) s = 0; printf "%d", s }')
    DIM_WORKFLOW_CONTRACT_NOTE=$(fmt_t note_workflow_deterministic "$M_WORKFLOW_CONTRACT_ERRORS" "$M_WORKFLOW_CONTRACT_WARNINGS")
  fi

  # D4: Structural Completeness (from Claude or deterministic)
  local d_structural=5
  if is_numeric_score "${CLAUDE_STRUCTURAL_COMPLETENESS:-}"; then
    d_structural="$CLAUDE_STRUCTURAL_COMPLETENESS"
    if awk -v s="$d_structural" 'BEGIN { exit !(s < 10) }'; then
      DIM_STRUCTURAL_NOTE=$(fmt_t note_structural_deep "$d_structural")
    fi
  else
    if [[ "$M_STRUCT_COMPLETENESS_TOTAL" -gt 0 ]]; then
      d_structural=$(awk -v p="$M_STRUCT_COMPLETENESS_PASS" -v t="$M_STRUCT_COMPLETENESS_TOTAL" \
        'BEGIN { printf "%d", (p / t) * 10 }')
    fi
    # Penalize TIER1 failures
    d_structural=$(awk -v s="$d_structural" -v t1="$TIER1_FAIL" \
      'BEGIN { r = s - (t1 * 1.5); if (r < 0) r = 0; printf "%d", r }')
    if awk -v s="$d_structural" 'BEGIN { exit !(s < 10) }'; then
      DIM_STRUCTURAL_NOTE=$(fmt_t note_structural_deterministic "$M_STRUCT_COMPLETENESS_PASS" "$M_STRUCT_COMPLETENESS_TOTAL" "$TIER1_FAIL")
    fi
  fi

  # D5: Agent Quality (from Claude or deterministic)
  local d_agent_quality=5
  if is_numeric_score "${CLAUDE_AGENT_QUALITY:-}"; then
    d_agent_quality="$CLAUDE_AGENT_QUALITY"
    if awk -v s="$d_agent_quality" 'BEGIN { exit !(s < 10) }'; then
      DIM_AGENT_QUALITY_NOTE=$(fmt_t note_agent_deep "$d_agent_quality")
    fi
  else
    # 5 sections checked, each gap = -1.5 from 10
    d_agent_quality=$(awk -v gaps="$M_AGENT_QUALITY_GAPS" \
      'BEGIN { s = 10 - (gaps * 1.5); if (s < 0) s = 0; printf "%d", s }')
    if awk -v s="$d_agent_quality" 'BEGIN { exit !(s < 10) }'; then
      DIM_AGENT_QUALITY_NOTE=$(fmt_t note_agent_deterministic "$M_AGENT_QUALITY_GAPS")
    fi
  fi

  # D6: Squad Agnosticism (from Claude or deterministic)
  local d_agnosticism=5
  if is_numeric_score "${CLAUDE_SQUAD_AGNOSTICISM:-}"; then
    d_agnosticism="$CLAUDE_SQUAD_AGNOSTICISM"
    if awk -v s="$d_agnosticism" 'BEGIN { exit !(s < 10) }'; then
      DIM_AGNOSTICISM_NOTE=$(fmt_t note_agnosticism_deep "$d_agnosticism")
    fi
  else
    if [[ "$M_AGNOSTICISM_VIOLATIONS" -eq 0 ]]; then
      d_agnosticism=10
    elif [[ "$M_AGNOSTICISM_VIOLATIONS" -eq 1 ]]; then
      d_agnosticism=8
    elif [[ "$M_AGNOSTICISM_VIOLATIONS" -le 2 ]]; then
      d_agnosticism=6
    elif [[ "$M_AGNOSTICISM_VIOLATIONS" -le 3 ]]; then
      d_agnosticism=4
    else
      d_agnosticism=2
    fi
    if awk -v s="$d_agnosticism" 'BEGIN { exit !(s < 10) }'; then
      DIM_AGNOSTICISM_NOTE=$(fmt_t note_agnosticism_deterministic "$M_AGNOSTICISM_VIOLATIONS")
    fi
  fi

  # D7: Production Evidence (from Claude or deterministic)
  local d_production=5
  if is_numeric_score "${CLAUDE_PRODUCTION_EVIDENCE:-}"; then
    d_production="$CLAUDE_PRODUCTION_EVIDENCE"
    if awk -v s="$d_production" 'BEGIN { exit !(s < 10) }'; then
      DIM_PRODUCTION_NOTE=$(fmt_t note_production_deep "$d_production")
    fi
  else
    d_production=$((PROD_SCORE * 2))
    [[ $d_production -gt 10 ]] && d_production=10
    if awk -v s="$d_production" 'BEGIN { exit !(s < 10) }'; then
      DIM_PRODUCTION_NOTE=$(fmt_t note_production_deterministic "$PROD_SCORE" "$PROD_MAX")
    fi
  fi

  # D8: Config Quality (from Claude or deterministic)
  local d_config=5
  if is_numeric_score "${CLAUDE_CONFIG_QUALITY:-}"; then
    d_config="$CLAUDE_CONFIG_QUALITY"
    if awk -v s="$d_config" 'BEGIN { exit !(s < 10) }'; then
      DIM_CONFIG_NOTE=$(fmt_t note_config_deep "$d_config")
    fi
  else
    local config_score=0
    local config_missing=""
    local workspace_level=""
    local output_root=""
    local config_total=8

    [[ -f "$SQUAD_DIR/config.yaml" ]] && config_score=$((config_score + 1)) || config_missing="${config_missing}config.yaml, "

    if grep -qE "^name:|^[[:space:]]+name:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      config_score=$((config_score + 1))
    else
      config_missing="${config_missing}name, "
    fi

    if grep -qE "^version:|^[[:space:]]+version:" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      config_score=$((config_score + 1))
    else
      config_missing="${config_missing}version, "
    fi

    if grep -q "entry_agent:" "$SQUAD_DIR/config.yaml" 2>/dev/null || [[ -n "${ENTRY_AGENT:-}" ]]; then
      config_score=$((config_score + 1))
    else
      config_missing="${config_missing}entry_agent, "
    fi

    if grep -qE "^tested:[[:space:]]*(true|yes)" "$SQUAD_DIR/config.yaml" 2>/dev/null; then
      config_score=$((config_score + 1))
    else
      config_missing="${config_missing}tested:true, "
    fi

    workspace_level=$(extract_workspace_integration_level)
    [[ -n "$workspace_level" ]] && config_score=$((config_score + 1)) || config_missing="${config_missing}workspace_integration.level, "

    output_root=$(extract_declared_output_root 2>/dev/null || true)
    [[ -n "$output_root" ]] && config_score=$((config_score + 1)) || config_missing="${config_missing}declared_output_root, "

    [[ "$M_VERSION_CONSISTENT" == "true" ]] && config_score=$((config_score + 1)) || config_missing="${config_missing}version_consistency, "

    d_config=$(awk -v p="$config_score" -v t="$config_total" 'BEGIN {
      if (t <= 0) { print 0; exit }
      s = (p / t) * 10
      if (s > 10) s = 10
      if (s < 0) s = 0
      printf "%d", int(s + 0.5)
    }')

    if awk -v s="$d_config" 'BEGIN { exit !(s < 10) }'; then
      config_missing="${config_missing%, }"
      if [[ -n "$config_missing" ]]; then
        DIM_CONFIG_NOTE=$(fmt_t note_config_missing "$config_missing" "$config_score" "$config_total")
      else
        DIM_CONFIG_NOTE=$(t note_config_generic)
      fi
    fi
  fi

  # D9: Documentation
  local d_documentation=5
  if is_numeric_score "${M_DOCUMENTATION:-}"; then
    d_documentation="$M_DOCUMENTATION"
    if awk -v s="$d_documentation" 'BEGIN { exit !(s < 10) }'; then
      DIM_DOCUMENTATION_NOTE=$(fmt_t note_documentation_deep "$d_documentation")
    fi
  else
    # Deterministic: based on README + ARCHITECTURE
    d_documentation=3
    local doc_missing=""
    [[ -f "$SQUAD_DIR/README.md" ]] && d_documentation=$((d_documentation + 3))
    [[ ! -f "$SQUAD_DIR/README.md" ]] && doc_missing="${doc_missing}README.md, "
    [[ -f "$SQUAD_DIR/ARCHITECTURE.md" ]] && d_documentation=$((d_documentation + 2))
    [[ ! -f "$SQUAD_DIR/ARCHITECTURE.md" ]] && doc_missing="${doc_missing}ARCHITECTURE.md, "
    [[ "$M_VERSION_CONSISTENT" == "true" ]] && d_documentation=$((d_documentation + 2))
    [[ "$M_VERSION_CONSISTENT" != "true" ]] && doc_missing="${doc_missing}version_consistency, "
    [[ $d_documentation -gt 10 ]] && d_documentation=10
    if awk -v s="$d_documentation" 'BEGIN { exit !(s < 10) }'; then
      doc_missing="${doc_missing%, }"
      DIM_DOCUMENTATION_NOTE=$(fmt_t note_documentation_deterministic "$doc_missing")
    fi
  fi

  # --- Weighted average ---
  # HIGH=1.5, MEDIUM=1.0, LOW=0.7
  local weighted_score
  weighted_score=$(awk \
    -v d1="$d_functionality" \
    -v d2="$d_security" \
    -v d3="$d_workflow_contract" \
    -v d4="$d_structural" \
    -v d5="$d_agent_quality" \
    -v d6="$d_agnosticism" \
    -v d7="$d_production" \
    -v d8="$d_config" \
    -v d9="$d_documentation" \
    'BEGIN {
      h = 1.5; m = 1.0; l = 0.7
      num = (d1*h) + (d2*h) + (d3*m) + (d4*m) + (d5*m) + (d6*h) + (d7*h) + (d8*m) + (d9*l)
      den = h + h + m + m + m + h + h + m + l
      printf "%.4f", num / den
    }')

  # --- Blocking issue penalties ---
  # Penalties are capped at -2.0 max to prevent false positives from destroying scores.
  # Security "secrets" in expert squads are often false positives (expert names, USD amounts).
  # TIER1_FAIL: -0.5 each, SEC_FAIL: -0.3 each, WF_CONTRACT_FAIL: -0.5, XREF_FAIL: -1.0 each
  # Cap: max total penalty = 2.0
  local penalty
  penalty=$(awk -v t1="$TIER1_FAIL" -v sec="$SEC_FAIL" -v wf="$WF_CONTRACT_FAIL" -v xr="$XREF_FAIL" \
    'BEGIN { p = (t1 * 0.5) + (sec * 0.3) + (wf * 0.5) + (xr * 1.0); if (p > 2.0) p = 2.0; printf "%.4f", p }')

  weighted_score=$(awk -v ws="$weighted_score" -v pen="$penalty" \
    'BEGIN { s = ws - pen; if (s < 0) s = 0; printf "%.4f", s }')

  local capped_score="$weighted_score"

  # Cap based on production evidence
  if [ "$PROD_SCORE" -eq 0 ]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 5) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 5) s = 5; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}production_cap:score<=5_without_production;"
    fi
  elif [ "$PROD_SCORE" -lt 3 ]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 7) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 7) s = 7; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}production_cap:score<=7_with_limited_evidence;"
    fi
  elif [ "$PROD_SCORE" -lt 5 ]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 9) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 9) s = 9; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}production_cap:score<=9_without_full_evidence;"
    fi
  fi

  # CRITICAL: If blocking issues exist, score NEVER > 6
  if [[ -n "$BLOCKING_ISSUES" ]]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 6) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 6) s = 6; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}blocking_issues_open:score<=6;"
    fi
  fi

  # PASS guardrails: severe debt in critical dimensions cannot produce PASS.
  local severe_high_count=0
  local severe_medium_count=0
  local severe_reasons=""

  if awk -v s="$d_functionality" 'BEGIN { exit !(s < 4) }'; then
    severe_high_count=$((severe_high_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:functionality=${d_functionality};"
  fi
  if awk -v s="$d_security" 'BEGIN { exit !(s < 4) }'; then
    severe_high_count=$((severe_high_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:security=${d_security};"
  fi
  if awk -v s="$d_agnosticism" 'BEGIN { exit !(s < 4) }'; then
    severe_high_count=$((severe_high_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:squad_agnosticism=${d_agnosticism};"
  fi
  if awk -v s="$d_production" 'BEGIN { exit !(s < 4) }'; then
    severe_high_count=$((severe_high_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:production_evidence=${d_production};"
  fi

  if awk -v s="$d_workflow_contract" 'BEGIN { exit !(s < 3) }'; then
    severe_medium_count=$((severe_medium_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:workflow_contract=${d_workflow_contract};"
  fi
  if awk -v s="$d_structural" 'BEGIN { exit !(s < 3) }'; then
    severe_medium_count=$((severe_medium_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:structural_completeness=${d_structural};"
  fi
  if awk -v s="$d_agent_quality" 'BEGIN { exit !(s < 3) }'; then
    severe_medium_count=$((severe_medium_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:agent_quality=${d_agent_quality};"
  fi
  if awk -v s="$d_config" 'BEGIN { exit !(s < 3) }'; then
    severe_medium_count=$((severe_medium_count + 1))
    severe_reasons="${severe_reasons}critical_dimension:config_quality=${d_config};"
  fi

  if [[ "$severe_high_count" -ge 2 ]] || [[ "$severe_high_count" -ge 1 && "$severe_medium_count" -ge 1 ]]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 5) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 5) s = 5; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}combined_critical_dimension_debt:score<=5;${severe_reasons}"
    fi
  elif [[ "$severe_high_count" -ge 1 ]]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 6) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 6) s = 6; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}critical_high_dimension_debt:score<=6;${severe_reasons}"
    fi
  elif [[ "$severe_medium_count" -ge 2 ]]; then
    if awk -v s="$capped_score" 'BEGIN { exit !(s > 6) }'; then
      capped_score=$(awk -v s="$capped_score" 'BEGIN { if (s > 6) s = 6; printf "%.4f", s }')
      SCORING_CAP_REASONS="${SCORING_CAP_REASONS}multiple_medium_dimension_debt:score<=6;${severe_reasons}"
    fi
  fi

  FINAL_SCORE_RAW=$(awk -v cs="$capped_score" 'BEGIN { printf "%.2f", cs }')
  FINAL_SCORE=$(round_score_0_10_int "$capped_score")

  # Store dimension scores for report
  DIM_FUNCTIONALITY="$d_functionality"
  DIM_SECURITY="$d_security"
  DIM_WORKFLOW_CONTRACT="$d_workflow_contract"
  DIM_STRUCTURAL="$d_structural"
  DIM_AGENT_QUALITY="$d_agent_quality"
  DIM_AGNOSTICISM="$d_agnosticism"
  DIM_PRODUCTION="$d_production"
  DIM_CONFIG="$d_config"
  DIM_DOCUMENTATION="$d_documentation"

  if [[ "$VERBOSE" == "true" ]]; then
    local pre_penalty_display
    local penalty_display
    local after_penalty_display
    local after_caps_display
    pre_penalty_display=$(awk -v ws="$weighted_score" -v pen="$penalty" 'BEGIN { printf "%.2f", ws + pen }')
    penalty_display=$(awk -v p="$penalty" 'BEGIN { printf "%.2f", p }')
    after_penalty_display=$(awk -v ws="$weighted_score" 'BEGIN { printf "%.2f", ws }')
    after_caps_display=$(awk -v cs="$capped_score" 'BEGIN { printf "%.2f", cs }')
    echo -e "\n  ${CYAN}$(t scoring_breakdown)${NC}"
    echo -e "    $(fmt_t weighted_avg "$pre_penalty_display")"
    echo -e "    $(fmt_t penalty "$penalty_display")"
    echo -e "    $(fmt_t after_penalty "$after_penalty_display")"
    echo -e "    $(fmt_t after_caps "$after_caps_display")"
    [[ -n "$SCORING_CAP_REASONS" ]] && echo -e "    $(fmt_t cap_reasons "$SCORING_CAP_REASONS")"
    echo -e "    $(fmt_t final_rounded "$FINAL_SCORE")"
  fi
}

generate_report() {
  local result="FAIL"
  local result_color=$RED
  local result_display

  # Coherent verdict logic
  if [[ $FINAL_SCORE -ge 7 ]] && [[ -z "$BLOCKING_ISSUES" ]]; then
    result="PASS"
    result_color=$GREEN
  elif [[ -n "$BLOCKING_ISSUES" ]] || [[ $FINAL_SCORE -lt 7 ]]; then
    if [[ $FINAL_SCORE -ge 4 ]]; then
      result="CONDITIONAL"
      result_color=$YELLOW
    else
      result="FAIL"
      result_color=$RED
    fi
  fi

  case "$result" in
    PASS) result_display=$(t verdict_pass) ;;
    CONDITIONAL) result_display=$(t verdict_conditional) ;;
    *) result_display=$(t verdict_fail) ;;
  esac

  # Helper: color a score
  score_color() {
    local s="$1"
    local display
    display=$(awk -v n="$s" '
      BEGIN {
        if (n < 0) n = 0;
        if (n > 10) n = 10;
        if (n == int(n)) printf "%d", n;
        else printf "%.1f", n;
      }')
    if awk -v n="$s" 'BEGIN { exit !(n >= 7) }'; then
      echo -e "${GREEN}${display}/10${NC}"
    elif awk -v n="$s" 'BEGIN { exit !(n >= 4) }'; then
      echo -e "${YELLOW}${display}/10${NC}"
    else
      echo -e "${RED}${display}/10${NC}"
    fi
  }

  if [[ "$JSON_OUTPUT" == "true" ]]; then
    # Escape improvements and priority fixes for JSON safety
    local json_improvements
    json_improvements=$(printf '%s' "${M_IMPROVEMENTS:-}" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read().strip()))' 2>/dev/null || echo '""')
    local json_priority_fixes
    json_priority_fixes=$(printf '%s' "${CLAUDE_EXEC_SUMMARY:-}" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read().strip()))' 2>/dev/null || echo '""')
    local json_blocking
    json_blocking=$(printf '%s' "${BLOCKING_ISSUES:-}" | python3 -c '
import json, sys
raw = sys.stdin.read().strip()
items = [line.strip() for line in raw.splitlines() if line.strip()]
print(json.dumps(items, ensure_ascii=False))
' 2>/dev/null || echo '[]')
    local json_score_guardrails
    json_score_guardrails=$(printf '%s' "${SCORING_CAP_REASONS:-}" | python3 -c '
import json, sys
raw = sys.stdin.read().strip()
items = [part.strip() for part in raw.split(";") if part.strip()]
print(json.dumps(items, ensure_ascii=False))
' 2>/dev/null || echo '[]')

    cat << ENDJSON
{
  "squad": "$SQUAD_NAME",
  "result": "$result",
  "analysis_language": "$ANALYSIS_LANG",
  "report_language": "$REPORT_LANG_RESOLVED",
  "localized_report_available": $LOCALIZED_REPORT_AVAILABLE,
  "final_score_raw": $FINAL_SCORE_RAW,
  "final_score": $FINAL_SCORE,
  "type": "$M_SQUAD_TYPE",
  "dimensions": {
    "functionality":           {"score": ${DIM_FUNCTIONALITY:-5}, "weight": "HIGH"},
    "security":                {"score": ${DIM_SECURITY:-5}, "weight": "HIGH"},
    "workflow_contract":       {"score": ${DIM_WORKFLOW_CONTRACT:-5}, "weight": "MEDIUM"},
    "structural_completeness": {"score": ${DIM_STRUCTURAL:-5}, "weight": "MEDIUM"},
    "agent_quality":           {"score": ${DIM_AGENT_QUALITY:-5}, "weight": "MEDIUM"},
    "squad_agnosticism":       {"score": ${DIM_AGNOSTICISM:-5}, "weight": "HIGH"},
    "production_evidence":     {"score": ${DIM_PRODUCTION:-5}, "weight": "HIGH"},
    "config_quality":          {"score": ${DIM_CONFIG:-5}, "weight": "MEDIUM"},
    "documentation":           {"score": ${DIM_DOCUMENTATION:-5}, "weight": "LOW"}
  },
  "metrics": {
    "agents": $M_AGENT_COUNT,
    "tasks": $M_TASK_COUNT,
    "checklists": $M_CHECKLIST_COUNT,
    "total_lines": $M_TOTAL_LINES
  },
  "structure": {
    "mandatory_checks": {
      "pass": $M_STRUCT_COMPLETENESS_PASS,
      "total": $M_STRUCT_COMPLETENESS_TOTAL,
      "tested_flag_present": $M_HAS_TESTED_FLAG,
      "architecture_doc_present": $M_HAS_ARCHITECTURE_DOC
    },
    "contextual_lifecycle_checks": {
      "pass": $M_CONTEXTUAL_LIFECYCLE_PASS,
      "total": $M_CONTEXTUAL_LIFECYCLE_TOTAL,
      "warnings": $M_CONTEXTUAL_LIFECYCLE_WARNINGS,
      "update_task_present": $M_HAS_UPDATE_TASK,
      "delete_task_present": $M_HAS_DELETE_TASK
    }
  },
  "deterministic": {
    "tier1_fail": $TIER1_FAIL,
    "security_fail": $SEC_FAIL,
    "xref_fail": $XREF_FAIL,
    "workflow_contract_fail": $WF_CONTRACT_FAIL,
    "agnosticism_violations": $M_AGNOSTICISM_VIOLATIONS,
    "agent_quality_gaps": $M_AGENT_QUALITY_GAPS,
    "warnings": $WARN_COUNT
  },
  "workflow_contracts": {
    "files_checked": $M_WORKFLOW_CONTRACT_FILES,
    "errors": $M_WORKFLOW_CONTRACT_ERRORS,
    "warnings": $M_WORKFLOW_CONTRACT_WARNINGS
  },
  "production": {
    "score": $PROD_SCORE,
    "max": $PROD_MAX
  },
  "claude_analysis": {
    "prompt_quality": ${M_PROMPT_QUALITY:-0},
    "structure_coherence": ${M_STRUCTURE_COHERENCE:-0},
    "coverage": ${M_COVERAGE_SCORE:-0},
    "documentation": ${M_DOCUMENTATION:-0},
    "quality_score": "$M_QUALITY_SCORE",
    "dimensional_scores": {
      "structural_completeness": ${CLAUDE_STRUCTURAL_COMPLETENESS:-0},
      "security_audit": ${CLAUDE_SECURITY_AUDIT:-0},
      "workflow_analysis": ${CLAUDE_WORKFLOW_ANALYSIS:-0},
      "agent_quality": ${CLAUDE_AGENT_QUALITY:-0},
      "squad_agnosticism": ${CLAUDE_SQUAD_AGNOSTICISM:-0},
      "config_quality": ${CLAUDE_CONFIG_QUALITY:-0},
      "production_evidence": ${CLAUDE_PRODUCTION_EVIDENCE:-0}
    }
  },
  "blocking_issues": $json_blocking,
  "score_guardrails": $json_score_guardrails,
  "improvements": $json_improvements,
  "priority_fixes": $json_priority_fixes
}
ENDJSON
  else
    # ═══════════════════════════════════════════════════════════════════════
    # VISUAL REPORT — 9 dimensional sections
    # ═══════════════════════════════════════════════════════════════════════
    echo ""
    echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${NC}"
    if [[ "$result" == "PASS" ]]; then
      printf "${BOLD}║${result_color}%60s${NC}${BOLD}║${NC}\n" "$(t validation_passed)"
    elif [[ "$result" == "CONDITIONAL" ]]; then
      printf "${BOLD}║${result_color}%60s${NC}${BOLD}║${NC}\n" "$(t validation_conditional)"
    else
      printf "${BOLD}║${result_color}%60s${NC}${BOLD}║${NC}\n" "$(t validation_failed)"
    fi
    echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    echo -e "  $(t label_squad): ${BOLD}$SQUAD_NAME${NC}"
    if [[ "$REPORT_LANG_RESOLVED" == "pt-br" ]]; then
      echo -e "  $(t label_type):  ${CYAN}$M_SQUAD_TYPE${NC} (confiança: $M_TYPE_CONFIDENCE/7)"
    else
      echo -e "  $(t label_type):  ${CYAN}$M_SQUAD_TYPE${NC} (confidence: $M_TYPE_CONFIDENCE/7)"
    fi
    echo -e "  $(t label_analysis_language): ${ANALYSIS_LANG}"
    echo -e "  $(t label_report_language): ${REPORT_LANG_RESOLVED}"
    echo -e "  $(t label_final): ${BOLD}${result_color}$FINAL_SCORE/10${NC}  |  $(t label_raw): ${BOLD}$FINAL_SCORE_RAW/10${NC}  |  $(t label_verdict): ${BOLD}${result_color}$result_display${NC}"
    echo ""

    # Section 1: Dimensional Scores Table
    echo -e "  ${BOLD}$(t dimensional_scores)${NC}"
    echo "  ┌──────────────────────────────┬────────┬────────┐"
    printf "  │ %-28s │ %-6s │ %-6s │\n" "$(t table_dimension)" "$(t table_score)" "$(t table_weight)"
    echo "  ├──────────────────────────────┼────────┼────────┤"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label functionality)" "$(score_color "${DIM_FUNCTIONALITY:-5}")" "$(weight_label HIGH)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label security)" "$(score_color "${DIM_SECURITY:-5}")" "$(weight_label HIGH)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label squad_agnosticism)" "$(score_color "${DIM_AGNOSTICISM:-5}")" "$(weight_label HIGH)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label production_evidence)" "$(score_color "${DIM_PRODUCTION:-5}")" "$(weight_label HIGH)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label workflow_contract)" "$(score_color "${DIM_WORKFLOW_CONTRACT:-5}")" "$(weight_label MEDIUM)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label structural_completeness)" "$(score_color "${DIM_STRUCTURAL:-5}")" "$(weight_label MEDIUM)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label agent_quality)" "$(score_color "${DIM_AGENT_QUALITY:-5}")" "$(weight_label MEDIUM)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label config_quality)" "$(score_color "${DIM_CONFIG:-5}")" "$(weight_label MEDIUM)"
    printf "  │ %-28s │ %s │ %-6s │\n" "$(dimension_label documentation)" "$(score_color "${DIM_DOCUMENTATION:-5}")" "$(weight_label LOW)"
    echo "  └──────────────────────────────┴────────┴────────┘"

    dimension_note() {
      local label="$1"
      case "$label" in
        functionality) printf "%s" "$DIM_FUNCTIONALITY_NOTE" ;;
        security) printf "%s" "$DIM_SECURITY_NOTE" ;;
        workflow_contract) printf "%s" "$DIM_WORKFLOW_CONTRACT_NOTE" ;;
        structural_completeness) printf "%s" "$DIM_STRUCTURAL_NOTE" ;;
        agent_quality) printf "%s" "$DIM_AGENT_QUALITY_NOTE" ;;
        squad_agnosticism) printf "%s" "$DIM_AGNOSTICISM_NOTE" ;;
        production_evidence) printf "%s" "$DIM_PRODUCTION_NOTE" ;;
        config_quality) printf "%s" "$DIM_CONFIG_NOTE" ;;
        documentation) printf "%s" "$DIM_DOCUMENTATION_NOTE" ;;
      esac
    }

    local has_dimension_notes=false
    for dim in functionality security workflow_contract structural_completeness agent_quality squad_agnosticism production_evidence config_quality documentation; do
      local score_var=""
      case "$dim" in
        functionality) score_var="${DIM_FUNCTIONALITY:-5}" ;;
        security) score_var="${DIM_SECURITY:-5}" ;;
        workflow_contract) score_var="${DIM_WORKFLOW_CONTRACT:-5}" ;;
        structural_completeness) score_var="${DIM_STRUCTURAL:-5}" ;;
        agent_quality) score_var="${DIM_AGENT_QUALITY:-5}" ;;
        squad_agnosticism) score_var="${DIM_AGNOSTICISM:-5}" ;;
        production_evidence) score_var="${DIM_PRODUCTION:-5}" ;;
        config_quality) score_var="${DIM_CONFIG:-5}" ;;
        documentation) score_var="${DIM_DOCUMENTATION:-5}" ;;
      esac
      if awk -v s="$score_var" 'BEGIN { exit !(s < 10) }'; then
        has_dimension_notes=true
        break
      fi
    done

    if [[ "$has_dimension_notes" == "true" ]]; then
      echo ""
      echo -e "  ${BOLD}$(t dimension_notes)${NC}"
      for dim in functionality security workflow_contract structural_completeness agent_quality squad_agnosticism production_evidence config_quality documentation; do
        local label=""
        local score_var=""
        case "$dim" in
          functionality) label="$(dimension_label functionality)"; score_var="${DIM_FUNCTIONALITY:-5}" ;;
          security) label="$(dimension_label security)"; score_var="${DIM_SECURITY:-5}" ;;
          workflow_contract) label="$(dimension_label workflow_contract)"; score_var="${DIM_WORKFLOW_CONTRACT:-5}" ;;
          structural_completeness) label="$(dimension_label structural_completeness)"; score_var="${DIM_STRUCTURAL:-5}" ;;
          agent_quality) label="$(dimension_label agent_quality)"; score_var="${DIM_AGENT_QUALITY:-5}" ;;
          squad_agnosticism) label="$(dimension_label squad_agnosticism)"; score_var="${DIM_AGNOSTICISM:-5}" ;;
          production_evidence) label="$(dimension_label production_evidence)"; score_var="${DIM_PRODUCTION:-5}" ;;
          config_quality) label="$(dimension_label config_quality)"; score_var="${DIM_CONFIG:-5}" ;;
          documentation) label="$(dimension_label documentation)"; score_var="${DIM_DOCUMENTATION:-5}" ;;
        esac
        if awk -v s="$score_var" 'BEGIN { exit !(s < 10) }'; then
          local note=""
          note=$(dimension_note "$dim")
          [[ -z "$note" ]] && note="score below 10 without explicit rationale captured"
          echo -e "    ${YELLOW}>${NC} $label: $note"
        fi
      done
    fi

    # Section 2: Blocking Issues
    if [[ -n "$BLOCKING_ISSUES" ]]; then
      echo ""
      echo -e "  ${BOLD}${RED}$(t blocking_issues)${NC}"
      echo -e "$BLOCKING_ISSUES" | while read -r issue; do
        [[ -n "$issue" ]] && echo -e "    ${RED}x${NC} $issue"
      done
    fi

    if [[ -n "$SCORING_CAP_REASONS" ]]; then
      echo ""
      echo -e "  ${BOLD}$(t score_guardrails)${NC}"
      echo "$SCORING_CAP_REASONS" | tr ';' '\n' | while read -r reason; do
        reason=$(echo "$reason" | xargs 2>/dev/null || echo "$reason")
        [[ -n "$reason" ]] && echo -e "    ${YELLOW}>${NC} $(translate_guardrail_reason "$reason")"
      done
    fi

    # Section 3: Deterministic Findings
    echo ""
    echo -e "  ${BOLD}$(t deterministic_findings)${NC}"
    echo "  ┌────────────────────────────┬───────┐"
    printf "  │ %-26s │ %-5s │\n" "$(t table_check)" "$(t table_count)"
    echo "  ├────────────────────────────┼───────┤"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label tier1)" "$TIER1_FAIL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label security)" "$SEC_FAIL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label xref)" "$XREF_FAIL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label workflow_contract)" "$WF_CONTRACT_FAIL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label agnosticism)" "$M_AGNOSTICISM_VIOLATIONS"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label agent_quality)" "$M_AGENT_QUALITY_GAPS/5"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label structural)" "$M_STRUCT_COMPLETENESS_PASS/$M_STRUCT_COMPLETENESS_TOTAL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label contextual_lifecycle)" "$M_CONTEXTUAL_LIFECYCLE_PASS/$M_CONTEXTUAL_LIFECYCLE_TOTAL"
    printf "  │ %-26s │ %-5s │\n" "$(deterministic_check_label warnings)" "$WARN_COUNT"
    echo "  └────────────────────────────┴───────┘"

    # Section 4: Production Evidence
    echo ""
    echo -e "  ${BOLD}$(dimension_label production_evidence)${NC}: $PROD_SCORE/$PROD_MAX"
    if [ "$PROD_SCORE" -eq 0 ]; then
      echo -e "    ${RED}$(t production_none)${NC}"
    elif [ "$PROD_SCORE" -lt 3 ]; then
      echo -e "    ${YELLOW}$(t production_limited)${NC}"
    else
      echo -e "    ${GREEN}$(t production_good)${NC}"
    fi

    # Section 5: Version Consistency
    if [[ "$M_VERSION_CONSISTENT" != "true" ]]; then
      echo ""
      echo -e "  ${BOLD}$(t version_consistency)${NC}: ${YELLOW}$(t version_mismatch)${NC}"
      [[ -n "$M_VERSION_DETAILS" ]] && echo -e "    $M_VERSION_DETAILS"
    fi

    # Section 6: Priority Fixes (from Claude or improvements)
    if [[ -n "$CLAUDE_EXEC_SUMMARY_REPORT" ]]; then
      echo ""
      echo -e "  ${BOLD}$(t priority_fixes)${NC}"
      printf '%s\n' "$CLAUDE_EXEC_SUMMARY_REPORT" | while IFS= read -r fix; do
        fix=$(echo "$fix" | xargs 2>/dev/null || echo "$fix")
        [[ -n "$fix" ]] && echo -e "    ${YELLOW}>${NC} $fix"
      done
    fi

    if [[ -n "$M_IMPROVEMENTS_REPORT" ]]; then
      echo ""
      echo -e "  ${BOLD}$(t improvements)${NC}"
      printf '%s\n' "$M_IMPROVEMENTS_REPORT" | while IFS= read -r imp; do
        imp=$(echo "$imp" | xargs 2>/dev/null || echo "$imp")
        [[ -n "$imp" ]] && echo -e "    - $imp"
      done
    fi

    echo ""
  fi

  VALIDATION_RESULT="$result"
  if [[ "$result" == "PASS" ]]; then
    EXIT_CODE=0
  else
    EXIT_CODE=1
  fi
}

# ═══════════════════════════════════════════════════════════════════════════════
# ORCHESTRATOR MODE
# ═══════════════════════════════════════════════════════════════════════════════
# When atomic scripts (validate-squad-structure.py, validate-squad-quality.py,
# validate-squad-deep.sh) are available, this script delegates to them in
# sequence. Falls back to legacy inline implementation if scripts are missing.
#
# Phases 0-2: validate-squad-structure.py (deterministic)
# Phase 3:    validate-squad-quality.py   (deterministic)
# Phases 4-6: validate-squad-deep.sh      (Claude CLI)
# ═══════════════════════════════════════════════════════════════════════════════

ATOMIC_STRUCTURE_SCRIPT="$SCRIPT_DIR/validate-squad-structure.py"
ATOMIC_QUALITY_SCRIPT="$SCRIPT_DIR/validate-squad-quality.py"
ATOMIC_DEEP_SCRIPT="$SCRIPT_DIR/validate-squad-deep.sh"

orchestrator_mode() {
  # Check if all atomic scripts exist
  local has_structure=false
  local has_quality=false
  local has_deep=false

  [[ -f "$ATOMIC_STRUCTURE_SCRIPT" ]] && has_structure=true
  [[ -f "$ATOMIC_QUALITY_SCRIPT" ]] && has_quality=true
  [[ -f "$ATOMIC_DEEP_SCRIPT" ]] && has_deep=true

  if [[ "$has_structure" == "false" ]] || [[ "$has_quality" == "false" ]]; then
    return 1  # Signal to use legacy mode
  fi

  echo ""
  echo "╔══════════════════════════════════════════════════════════════╗"
  echo "║        🔍 VALIDATE-SQUAD v4.0 (Squad Creator)               ║"
  echo "╠══════════════════════════════════════════════════════════════╣"
  echo "║                                                              ║"
  echo "║  Squad:     $SQUAD_NAME"
  echo "║  Path:      $SQUAD_DIR"
  echo "║  Runtime:   $SELECTED_RUNTIME"
  echo "║  Model:     $MODEL_QUALITY"
  echo "║  Mode:      orchestrator (atomic scripts)"
  echo "║                                                              ║"
  echo "╠══════════════════════════════════════════════════════════════╣"
  echo "║  Execution Plan:                                             ║"
  echo "║  ┌─────────────────────────────────────────────────────────┐ ║"
  echo "║  │ Phase 1: Structure          (deterministic — Python)    │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 2: Agnosticism        (deterministic — Bash)      │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 3: Cross-References   (deterministic — Bash)      │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 4: Quality            (deterministic — Python)    │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 5: Deep Review        (LLM — $SELECTED_RUNTIME)  │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 6: Production Evidence (deterministic — Bash)     │ ║"
  echo "║  │    ↓                                                    │ ║"
  echo "║  │ Phase 7: Final Score        (deterministic — Bash)      │ ║"
  echo "║  └─────────────────────────────────────────────────────────┘ ║"
  echo "║                                                              ║"
  echo "╚══════════════════════════════════════════════════════════════╝"
  echo ""

  PIPELINE_START_TIME=$(date +%s)

  # Dry run: show plan and exit
  if [[ "$DRY_RUN" == "true" ]]; then
    echo "🔍 DRY RUN — would validate squad: $SQUAD_NAME"
    echo "   Phases: 1 (Structure) → 2 (Agnosticism) → 3 (Cross-Refs) → 4 (Quality) → 5 (Deep Review) → 6 (Production) → 7 (Score)"
    echo "   Runtime: $SELECTED_RUNTIME | Model: $MODEL_QUALITY"
    exit 0
  fi

  # ─── Phase 1: Structure ───
  runtime_state_phase_start "phase_1_structure"
  echo "╔══════════════════════════════════════════════════════════════╗"
  echo "║  📌 PHASE 1/7: Structure — $(date +%H:%M:%S)"
  echo "╚══════════════════════════════════════════════════════════════╝"
  local structure_output=""
  local structure_exit=0
  local structure_json="{}"

  if structure_output=$(python3 "$ATOMIC_STRUCTURE_SCRIPT" "$SQUAD_DIR" --output json 2>&1); then
    structure_exit=0
    echo -e "  ${GREEN}✓${NC} Structure validation passed"
  else
    structure_exit=$?
    if [[ $structure_exit -eq 1 ]]; then
      echo -e "  ${RED}✗${NC} Structure validation found issues"
    else
      echo -e "  ${RED}✗${NC} Structure validation error"
    fi
  fi

  structure_json=$(printf "%s" "$structure_output" | extract_first_json_object)
  if [[ -n "$structure_json" ]] && [[ "$structure_json" != "{}" ]]; then
    local structure_fields=""
    structure_fields=$(extract_structure_fields "$structure_json")
    while IFS=$'\t' read -r key value; do
      case "$key" in
        squad_type) M_SQUAD_TYPE="$value" ;;
        type_confidence) M_TYPE_CONFIDENCE="$value" ;;
        agents) M_AGENT_COUNT="$value" ;;
        tasks) M_TASK_COUNT="$value" ;;
        workflows) : ;;
        checklists) M_CHECKLIST_COUNT="$value" ;;
        structure_valid) : ;;
        blocking_issue_count) : ;;
        warning_count)
          if [[ "$value" =~ ^[0-9]+$ ]]; then
            WARN_COUNT="$value"
          fi
          ;;
        security_issue_count)
          if [[ "$value" =~ ^[0-9]+$ ]]; then
            SEC_FAIL="$value"
            M_SECURITY_ISSUES="$value"
          fi
          ;;
        non_security_blocking_count)
          if [[ "$value" =~ ^[0-9]+$ ]]; then
            TIER1_FAIL="$value"
          fi
          ;;
        blocking_issues_b64)
          BLOCKING_ISSUES=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "", end="")' 2>/dev/null || true)
          if [[ -n "$BLOCKING_ISSUES" ]] && [[ "${BLOCKING_ISSUES: -1}" != $'\n' ]]; then
            BLOCKING_ISSUES+=$'\n'
          fi
          ;;
        warnings_b64)
          WARNINGS=$(printf '%s' "$value" | python3 -c 'import sys,base64; data=sys.stdin.read().strip(); print(base64.b64decode(data).decode("utf-8") if data else "", end="")' 2>/dev/null || true)
          if [[ -n "$WARNINGS" ]] && [[ "${WARNINGS: -1}" != $'\n' ]]; then
            WARNINGS+=$'\n'
          fi
          ;;
      esac
    done <<< "$structure_fields"
  fi

  collect_orchestrator_baseline
  runtime_state_phase_complete "phase_1_structure" "$([[ $structure_exit -eq 0 ]] && echo completed || echo failed)"

  if [[ "$VERBOSE" == "true" ]] && [[ -n "$structure_json" ]] && [[ "$structure_json" != "{}" ]]; then
    python3 -c "
import json, sys
d = json.loads(sys.stdin.read())
c = d.get('coverage', {})
print(f'  Coverage: {c.get(\"agents\",0)} agents, {c.get(\"tasks\",0)} tasks, {c.get(\"workflows\",0)} workflows, {c.get(\"checklists\",0)} checklists')
print(f'  Type: {d.get(\"squad_type\",\"?\")} (confidence: {d.get(\"type_confidence\",\"?\")}/7)')
print(f'  Structure score: {d.get(\"score\",\"?\")}/100')
bi = d.get('blocking_issues', [])
if bi:
    print(f'  Blocking issues ({len(bi)}):')
    for i in bi: print(f'    - {i}')
" <<< "$structure_json" 2>/dev/null || true
  fi

  # ─── Phase 3: Quality (only if structure passed) ───
  local quality_exit=1
  if [[ $structure_exit -ne 2 ]]; then
    runtime_state_phase_start "phase_6_quality_analysis"
    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  📌 PHASE 4/7: Quality — $(date +%H:%M:%S)"
    echo "╚══════════════════════════════════════════════════════════════╝"
    local quality_output=""

    if quality_output=$(python3 "$ATOMIC_QUALITY_SCRIPT" "$SQUAD_DIR" --output json 2>&1); then
      quality_exit=0
      echo -e "  ${GREEN}✓${NC} Quality analysis passed"
    else
      quality_exit=$?
      echo -e "  ${YELLOW}⚠${NC} Quality analysis found issues (exit=$quality_exit)"
    fi

    if [[ "$VERBOSE" == "true" ]] && [[ -n "$quality_output" ]]; then
      local quality_json
      quality_json=$(printf "%s" "$quality_output" | extract_first_json_object 2>/dev/null)
      if [[ -n "$quality_json" ]] && [[ "$quality_json" != "{}" ]]; then
        python3 -c "
import json, sys
d = json.loads(sys.stdin.read())
print(f'  Task Anatomy: {d.get(\"task_anatomy_coverage\",\"?\")}')
print(f'  Acceptance Criteria: {d.get(\"acceptance_criteria_coverage\",\"?\")}')
print(f'  Workflows + State Machine: {d.get(\"workflows_with_state_machine\",\"?\")}')
print(f'  Workflows + task_ref: {d.get(\"workflows_with_task_ref\",\"?\")}')
print(f'  Quality score: {d.get(\"score\",\"?\")}/100')
issues = [i for i in d.get('issues',[]) if not i.startswith('Monolithic')]
if issues:
    task_issues = [i for i in issues if 'Task missing' in i]
    other = [i for i in issues if 'Task missing' not in i]
    if task_issues:
        print(f'  Tasks missing anatomy: {len(task_issues)}')
    for i in other[:5]: print(f'    - {i}')
" <<< "$quality_json" 2>/dev/null || true
      fi
    fi

    runtime_state_phase_complete "phase_6_quality_analysis" "$([[ $quality_exit -eq 0 ]] && echo completed || echo failed)"
  else
    echo ""
    echo -e "${YELLOW}⚠${NC} Skipping quality analysis (structure validation error)"
  fi

  # ─── Phases 4-6: Deep Review (only if quality passed or --force-deep) ───
  if [[ "$has_deep" == "true" ]]; then
    local run_deep=false
    if [[ "${FORCE_DEEP:-0}" == "1" ]]; then
      run_deep=true
    elif [[ $quality_exit -ne 2 ]] && [[ "$QUICK_MODE" != "true" ]]; then
      run_deep=true
    fi

    if [[ "$run_deep" == "true" ]]; then
      runtime_state_phase_start "phase_6_deep_review"
      echo ""
      echo "╔══════════════════════════════════════════════════════════════╗"
      echo "║  📌 PHASE 5/7: Deep Review (LLM — $SELECTED_RUNTIME) — $(date +%H:%M:%S)"
      echo "╚══════════════════════════════════════════════════════════════╝"
      local deep_output=""
      local deep_args=("$SQUAD_DIR" "--model" "$MODEL_QUALITY")

      # Build findings file from previous deterministic phases for injection into LLM
      local findings_tmp
      findings_tmp=$(mktemp "${TMPDIR:-/tmp}/validate-findings.XXXXXX")
      cat > "$findings_tmp" << FINDINGS_END
### Structure (Phase 1) — deterministic
- Squad type: $M_SQUAD_TYPE (confidence: $M_TYPE_CONFIDENCE/7)
- Agents: $M_AGENT_COUNT | Tasks: $M_TASK_COUNT | Checklists: $M_CHECKLIST_COUNT
- TIER1 failures: $TIER1_FAIL
- Security issues: $SEC_FAIL
- Structural checks: $M_STRUCT_COMPLETENESS_PASS/$M_STRUCT_COMPLETENESS_TOTAL
- Version consistent: $M_VERSION_CONSISTENT

### Quality (Phase 4) — deterministic
$(if [[ -n "${quality_output:-}" ]]; then
  printf "%s" "$quality_output" | python3 -c "
import json, sys
try:
    d = json.loads(sys.stdin.read().strip().split('{',1)[1].rsplit('}',1)[0].join(['[{','}]']) if '{' in sys.stdin.read() else '{}')
except: d = {}
d = json.loads(open('/dev/stdin').read()) if False else {}
" 2>/dev/null || true
  # Simpler: extract key metrics
  printf "%s" "$quality_output" | python3 -c "
import json, sys
for line in sys.stdin:
    line = line.strip()
    if not line or line[0] != '{': continue
    try:
        d = json.loads(line)
        print(f'- Task Anatomy coverage: {d.get(\"task_anatomy_coverage\",\"?\")}')
        print(f'- Acceptance Criteria: {d.get(\"acceptance_criteria_coverage\",\"?\")}')
        print(f'- Workflows + state machine: {d.get(\"workflows_with_state_machine\",\"?\")}')
        print(f'- Workflows + task_ref: {d.get(\"workflows_with_task_ref\",\"?\")}')
        print(f'- Quality score: {d.get(\"score\",\"?\")}/100')
        break
    except: pass
" 2>/dev/null || echo "- (quality output not parseable)"
fi)

### Agnosticism (Phase 2) — deterministic
- Violations: $M_AGNOSTICISM_VIOLATIONS

### Cross-References (Phase 3) — deterministic
- Broken refs: $XREF_FAIL
- Workflow contract errors: $M_WORKFLOW_CONTRACT_ERRORS

### Production (Phase 6) — deterministic
- Production score: $PROD_SCORE/$PROD_MAX
FINDINGS_END
      deep_args+=("--findings" "$findings_tmp")

      if deep_output=$(bash "$ATOMIC_DEEP_SCRIPT" "${deep_args[@]}" 2>&1); then
        rm -f "$findings_tmp"
        echo -e "  ${GREEN}✓${NC} Deep review complete"
        local deep_json="{}"
        deep_json=$(printf "%s" "$deep_output" | extract_first_json_object)
        if [[ -n "$deep_json" ]] && [[ "$deep_json" != "{}" ]]; then
          hydrate_deep_review_from_envelope "$deep_json"
        fi
        runtime_state_phase_complete "phase_6_deep_review"
      else
        rm -f "$findings_tmp"
        echo -e "  ${YELLOW}⚠${NC} Deep review returned non-zero exit"
        runtime_state_phase_complete "phase_6_deep_review" "failed"
      fi

      # Evaluator: cheap LLM validates deep review quality (Haiku/Flash/Spark)
      if [[ -n "$deep_json" ]] && [[ "$deep_json" != "{}" ]] && [[ "$HAS_RUNTIME_LIB" == "true" ]]; then
        local eval_model="$MODEL_FAST"
        local eval_prompt_file
        eval_prompt_file=$(mktemp)
        cat > "$eval_prompt_file" << 'EVALEOF'
Evaluate this squad validation JSON. Check:
1. All 7 dimension scores are present and between 0-10
2. executive_summary has overall_score, verdict, priority_fixes, strengths
3. No dimension score contradicts its own detail (e.g. score 9 but all items FAIL)
Reply with ONLY one word: VALID or INVALID
EVALEOF
        printf '\n\nJSON to evaluate:\n%s' "$(echo "$deep_json" | head -100)" >> "$eval_prompt_file"

        local saved_mt="${PHASE_MAX_TURNS:-}"
        local saved_at="${PHASE_ALLOWED_TOOLS:-}"
        PHASE_MAX_TURNS="1"
        PHASE_ALLOWED_TOOLS=""
        local eval_out_file
        eval_out_file=$(mktemp)
        _exec_runtime "$eval_model" "$eval_prompt_file" "$eval_out_file" 2>/dev/null || true
        local eval_verdict
        eval_verdict=$(grep -oiE "VALID|INVALID" "$eval_out_file" | head -1)
        PHASE_MAX_TURNS="$saved_mt"
        PHASE_ALLOWED_TOOLS="$saved_at"
        rm -f "$eval_prompt_file" "$eval_out_file"

        if [[ "$eval_verdict" == "INVALID" ]]; then
          echo -e "  ${YELLOW}🔍 Evaluator ($eval_model): INVALID — deep review may have structural issues${NC}"
        else
          echo -e "  ${GREEN}🔍 Evaluator ($eval_model): VALID${NC}"
        fi
      fi

      if [[ "$VERBOSE" == "true" ]] && [[ -n "$deep_json" ]] && [[ "$deep_json" != "{}" ]]; then
        python3 -c "
import json, sys
d = json.loads(sys.stdin.read())
a = d.get('analysis', d)
for section in ['structural_completeness', 'security_audit', 'workflow_analysis', 'agent_quality', 'squad_agnosticism', 'config_quality', 'production_evidence']:
    s = a.get(section, {})
    score = s.get('score', '?')
    print(f'  {section}: {score}/10')
es = a.get('executive_summary', {})
if es:
    print(f'  Overall: {es.get(\"overall_score\",\"?\")}/10 — {es.get(\"verdict\",\"?\")}')
    for fix in es.get('priority_fixes', [])[:3]:
        print(f'    → {fix[:80]}')
" <<< "$deep_json" 2>/dev/null || true
      fi
    elif [[ "$QUICK_MODE" == "true" ]]; then
      echo ""
      echo -e "${YELLOW}⚠${NC} Skipping deep review (--quick mode)"
    else
      echo ""
      echo -e "${YELLOW}⚠${NC} Skipping deep review (quality analysis error)"
    fi
  fi

  return 0
}

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN EXECUTION
# ═══════════════════════════════════════════════════════════════════════════════

main() {
  runtime_state_start

  # Orchestrator path: consume atomic scripts, then run only supplemental gates
  if orchestrator_mode 2>/dev/null; then
    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  📌 PHASE 2/7: Squad Agnosticism — $(date +%H:%M:%S)"
    echo "╚══════════════════════════════════════════════════════════════╝"
    runtime_state_phase_start "phase_2_5_squad_agnosticism"
    check_squad_agnosticism
    runtime_state_phase_complete "phase_2_5_squad_agnosticism"

    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  📌 PHASE 3/7: Cross-References — $(date +%H:%M:%S)"
    echo "╚══════════════════════════════════════════════════════════════╝"
    runtime_state_phase_start "phase_3_cross_reference"
    check_cross_references
    runtime_state_phase_complete "phase_3_cross_reference"

    runtime_state_phase_start "phase_3_5_workflow_contracts"
    check_workflow_contracts
    runtime_state_phase_complete "phase_3_5_workflow_contracts"

    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  📌 PHASE 6/7: Production Evidence — $(date +%H:%M:%S)"
    echo "╚══════════════════════════════════════════════════════════════╝"
    runtime_state_phase_start "phase_5_production_validation"
    check_production
    runtime_state_phase_complete "phase_5_production_validation"

    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║  📌 PHASE 7/7: Final Score — $(date +%H:%M:%S)"
    echo "╚══════════════════════════════════════════════════════════════╝"
    runtime_state_phase_start "phase_7_final_scoring"
    calculate_final_score
    generate_report
    runtime_state_phase_complete "phase_7_final_scoring"

    local PIPELINE_END_TIME
    PIPELINE_END_TIME=$(date +%s)
    local TOTAL_DURATION=$((PIPELINE_END_TIME - PIPELINE_START_TIME))
    local TOTAL_MINUTES=$((TOTAL_DURATION / 60))
    local TOTAL_SECONDS=$((TOTAL_DURATION % 60))

    # ─── Save reports to disk (like sinkra-validate.sh) ─────────────
    local REPORT_DIR="$WORKSPACE_ROOT/outputs/squad-validations/$SQUAD_NAME/$(date +%Y%m%d-%H%M%S)"
    mkdir -p "$REPORT_DIR"

    # Save JSON report
    JSON_OUTPUT=true generate_report > "$REPORT_DIR/score_card.json" 2>/dev/null
    JSON_OUTPUT=""

    # Save score summary YAML
    cat > "$REPORT_DIR/score_card.yaml" << SCOREEOF
validation:
  squad: "$SQUAD_NAME"
  squad_path: "$SQUAD_DIR"
  validated_by: "validate-squad.sh v4.0"
  validated_date: "$(date -Iseconds)"
  runtime: "$SELECTED_RUNTIME"
  model: "$MODEL_QUALITY"
  duration_seconds: $TOTAL_DURATION

scores:
  final: $FINAL_SCORE
  raw: $FINAL_SCORE_RAW
  verdict: "$VALIDATION_RESULT"
  type: "$M_SQUAD_TYPE"

dimensions:
  functionality: ${DIM_FUNCTIONALITY:-5}
  security: ${DIM_SECURITY:-5}
  workflow_contract: ${DIM_WORKFLOW_CONTRACT:-5}
  structural_completeness: ${DIM_STRUCTURAL:-5}
  agent_quality: ${DIM_AGENT_QUALITY:-5}
  squad_agnosticism: ${DIM_AGNOSTICISM:-5}
  production_evidence: ${DIM_PRODUCTION:-5}
  config_quality: ${DIM_CONFIG:-5}
  documentation: ${DIM_DOCUMENTATION:-5}

metrics:
  agents: $M_AGENT_COUNT
  tasks: $M_TASK_COUNT
  checklists: $M_CHECKLIST_COUNT
SCOREEOF

    # Save deep review JSON if available
    if [[ -n "${CLAUDE_RAW_JSON:-}" ]] && [[ "$CLAUDE_RAW_JSON" != "{}" ]]; then
      printf '%s' "$CLAUDE_RAW_JSON" | python3 -m json.tool > "$REPORT_DIR/deep_review.json" 2>/dev/null || true
    fi

    # Symlink latest
    ln -sfn "$(basename "$REPORT_DIR")" "$(dirname "$REPORT_DIR")/latest"

    echo ""
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║                                                              ║"
    if [[ "$EXIT_CODE" -eq 0 ]]; then
      echo "║        ✅ VALIDATION COMPLETE — PASS                         ║"
    else
      echo "║        ⚠️  VALIDATION COMPLETE — ISSUES FOUND                ║"
    fi
    echo "║                                                              ║"
    echo "║  Squad:     $SQUAD_NAME"
    echo "║  Score:     $FINAL_SCORE/10"
    echo "║  Verdict:   $VALIDATION_RESULT"
    echo "║  Duration:  ${TOTAL_MINUTES}m ${TOTAL_SECONDS}s"
    echo "║  Report:    $REPORT_DIR"
    echo "║                                                              ║"
    echo "╚══════════════════════════════════════════════════════════════╝"

    # Show cost summary if metrics lib is loaded
    if [[ "$HAS_METRICS_LIB" == "true" ]] && type show_cost_summary &>/dev/null; then
      show_cost_summary
    fi

    # Append to progress log
    _progress_log "Result: $FINAL_SCORE/10 ($VALIDATION_RESULT) in ${TOTAL_MINUTES}m${TOTAL_SECONDS}s"
    _progress_log "Report: $REPORT_DIR"

    if [[ "$EXIT_CODE" -eq 0 ]]; then
      runtime_state_complete "completed"
    else
      runtime_state_complete "failed"
    fi

    exit "$EXIT_CODE"
  fi

  echo ""
  echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${NC}"
  printf "${BOLD}║ %-60s ${NC}${BOLD}║${NC}\n" "$(t main_title)"
  echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${NC}"
  echo ""
  echo -e "  $(t label_squad): ${CYAN}$SQUAD_NAME${NC}"
  echo -e "  $(t label_path): $SQUAD_DIR"
  if [[ "$QUICK_MODE" == "true" ]]; then
    echo -e "  $(t label_mode): $(t mode_quick)"
  else
    echo -e "  $(t label_mode): $(t mode_hybrid)"
  fi
  echo -e "  $(t label_model): $MODEL_QUALITY"

  # LEGACY: full implementation below -- used as fallback if atomic scripts not found
  # or for full scoring/reporting which the orchestrator does not handle

  # Phase 1: Structure (Bash)
  runtime_state_phase_start "phase_1_structure"
  check_structure
  runtime_state_phase_complete "phase_1_structure"

  # Phase 2: Security (Bash)
  runtime_state_phase_start "phase_2_security_scan"
  check_security
  runtime_state_phase_complete "phase_2_security_scan"

  # Phase 2.5: Squad Agnosticism (Bash)
  runtime_state_phase_start "phase_2_5_squad_agnosticism"
  check_squad_agnosticism
  runtime_state_phase_complete "phase_2_5_squad_agnosticism"

  # Phase 3: Cross-references (Bash)
  runtime_state_phase_start "phase_3_cross_reference"
  check_cross_references
  runtime_state_phase_complete "phase_3_cross_reference"

  # Phase 3.5: Workflow contracts (same validator as CI)
  runtime_state_phase_start "phase_3_5_workflow_contracts"
  check_workflow_contracts
  runtime_state_phase_complete "phase_3_5_workflow_contracts"

  # Phase 3.7: Output Path Governance (Bash)
  runtime_state_phase_start "phase_3_7_output_path_governance"
  check_output_path_governance
  runtime_state_phase_complete "phase_3_7_output_path_governance"

  # Phase 4: Type detection (Bash)
  runtime_state_phase_start "phase_4_type_detection"
  detect_squad_type
  runtime_state_phase_complete "phase_4_type_detection"

  # Phase 5: Production validation (Bash) - NEW
  runtime_state_phase_start "phase_5_production_validation"
  check_production
  runtime_state_phase_complete "phase_5_production_validation"

  # Phase 6: Quality analysis (Claude CLI)
  runtime_state_phase_start "phase_6_quality_analysis"
  analyze_with_claude
  runtime_state_phase_complete "phase_6_quality_analysis"

  # Phase 7: Final scoring
  runtime_state_phase_start "phase_7_final_scoring"
  calculate_final_score

  # Generate report
  generate_report
  runtime_state_phase_complete "phase_7_final_scoring"

  if [[ "$EXIT_CODE" -eq 0 ]]; then
    runtime_state_complete "completed"
  else
    runtime_state_complete "failed"
  fi

  exit "$EXIT_CODE"
}

# Run
main
