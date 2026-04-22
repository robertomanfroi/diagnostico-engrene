# Task: Create Pipeline — Render

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline-render` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-pipeline-render
name: "Create Pipeline — Render"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Renderiza shell runner, prompt template, agent summaries, lib/ e handlers a partir do contrato de design. Incorpora 14 lições do post-mortem domain-decoder."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_pipeline_render
Output: artifact::create_pipeline_render
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Converter o design do pipeline em um conjunto executável de arquivos.
O shell runner (.sh) é o deliverable PRINCIPAL — sem ele, tudo é inútil.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `pipeline_design_contract` | object | Yes | Contrato de design (fases, componentes, layout) |

## Deliverables (ALL required — VETO se ausente)

| # | Arquivo | Obrigatoriedade | Descrição |
|---|---------|-----------------|-----------|
| 1 | `scripts/{squad}.sh` | **VETO** | CLI entry point — o que o usuário executa |
| 2 | `templates/pipeline/prompt.md` | **VETO** | Prompt com placeholders para injeção |
| 3 | `agents/summaries/*.md` | RECOMENDADO | ~2K chars por agent com expertise + approach |
| 4 | `lib/pipeline_state.py` | SIM | State manager |
| 5 | `lib/phase_runner.py` | SIM | Phase execution loop |
| 6 | `lib/progress.py` | SIM | Progress tracker |
| 7 | `lib/handlers/` | SIM (se 5+ fases) | Um handler por fase |

## Workflow

### Step 1: Gerar Shell Runner (PRINCIPAL)

O `.sh` DEVE implementar estes padrões (extraídos de 14 bugs encontrados em produção):

#### 1A. Bootstrap e Interface

```bash
# Bootstrap runner-lib v2
source "$RUNNER_LIB_DIR/pipeline-bootstrap.sh"

# Aceitar flags padrão:
#   --source <path>   (obrigatório — path do codebase alvo)
#   --model <name>    (opus, sonnet, haiku)
#   --phase <num>     (resume de fase específica)
#   --claude/--codex/--gemini
#   --help
```

**Regra B03:** Slug auto-derivado do `--source`. NUNCA como argumento posicional obrigatório.
**Regra B04:** Versão auto-detectada do source (package.json → config.yaml → fallback).
**Regra B02:** Modo default = `auto` (detecta greenfield/brownfield via state file).

#### 1B. LLM Invocation (CRÍTICO — 4 bugs aqui)

```bash
decoder_run_llm() {
  local model="$1" prompt="$2" log_file="$3"

  # REGRA B12: Escalar turns por modelo
  local default_turns=10
  case "$model" in
    *haiku*) default_turns=12 ;;
    *sonnet*) default_turns=10 ;;
    *opus*)  default_turns=15 ;;
  esac
  PHASE_MAX_TURNS="${OVERRIDE_MAX_TURNS:-$default_turns}"

  # REGRA B12: Restringir tools permitidas
  PHASE_ALLOWED_TOOLS="Read,Write,Glob,Grep,Bash(ls),Bash(wc),Bash(head)"

  local raw_output
  raw_output=$(claude -p --model "$model" \
    --max-turns "$PHASE_MAX_TURNS" \
    --allowedTools "$PHASE_ALLOWED_TOOLS" \
    --dangerously-skip-permissions "$prompt" 2>&1 | tee -a "$log_file")

  # REGRA B10: Filtrar JSON metadata de claude -p
  echo "$raw_output" | grep -v '^{"type":"result"' | grep -v '^{"error":'
}
```

#### 1C. Output Handling (CRÍTICO — 3 bugs aqui)

```bash
# REGRA B11: Script SEMPRE salva output (não depende do LLM usar Write)
if [[ "$output_chars" -gt 200 ]]; then
  echo "$OUTPUT" > "$phase_out_dir/phase${phase_num}-output.md"
fi

# REGRA B07: Buscar PHASE_COMPLETE apenas nas últimas 30 linhas
OUTPUT_TAIL="$(echo "$OUTPUT" | tail -30)"
if echo "$OUTPUT_TAIL" | grep -q "<promise>PHASE_COMPLETE</promise>"; then
  ...
fi

# REGRA B10: Threshold de completion POR FASE (não fixo em 500)
case "$phase_num" in
  0) phase_min_chars=3000 ;;
  1) phase_min_chars=3000 ;;
  2) phase_min_chars=4000 ;;
  *) phase_min_chars=3000 ;;
esac
```

#### 1D. Gate Validation (CRÍTICO — 4 bugs aqui)

```bash
# REGRA B05: Gate ANTES de marcar complete
validate_phase_gate "$phase_num"
if [[ $? -eq 0 ]]; then
  mark_complete  # SÓ se gate passou
else
  mark_in_progress  # Revert se gate falhou
fi

# REGRA B06: Regex contextual para markers
grep -lE "^(VETO|BLOCKED|FAILED)|status:\s*(VETO|BLOCKED|FAILED)" ...

# REGRA B08: find -exec em vez de glob para dirs vazios
find "$out_path" -maxdepth 1 -name "*.md" -exec grep ... {} +

# REGRA B09: jq com --arg (nunca interpolar shell vars)
jq --arg reason "$veto_reason" '.error = $reason' "$STATE_FILE"

# REGRA B14: Gates de arquivo separado = WARNING, não BLOCKING
echo "⚠️ E7: dedup-matrix.md not found (may be in phase output)"
```

#### 1E. Context Injection (PADRÃO MMOS — 2 bugs aqui)

```bash
build_phase_prompt() {
  local phase_num="$1" prior_context="$2"

  # REGRA B13: Injetar prior outputs INLINE (não como paths para ler)
  # REGRA Gap3: Injetar task content INLINE
  # REGRA Gap5: Injetar agent summary INLINE
  local task_content="$(build_task_content "$phase_num")"
  local agent_summary="$(build_agent_summary "$phase_num")"
  local checklist_content="$(build_checklist_content "$phase_num")"

  # Substituir placeholders no template
  template="${template//\{AGENT_SUMMARY\}/$agent_summary}"
  template="${template//\{TASK_CONTENT\}/$task_content}"
  template="${template//\{CHECKLIST_CONTENT\}/$checklist_content}"
}
```

#### 1F. Retry Boost

```bash
# REGRA: Na iter 2+, informar o que faltou
if [[ "$iter" -gt 1 ]]; then
  RETRY_BOOST="## RETRY (attempt $iter)
Previous attempt was insufficient. Issues to fix:
- Text response must be over $phase_min_chars characters
- Create EACH mandatory artifact file
- You already created $existing_files files — create MISSING ones
- End with <promise>PHASE_COMPLETE</promise>"
fi
```

### Step 2: Gerar Prompt Template

O `templates/pipeline/prompt.md` DEVE ter:

```markdown
# Pipeline — Phase {FORCE_PHASE}

System: **{SYSTEM_SLUG}** | Source: `{SOURCE_PATH}` | Output: `{SYSTEM_DIR}`

## Agent Expertise (Who You Are)
{AGENT_SUMMARY}

## Task Instructions (What To Do)
{TASK_CONTENT}

## Phase {FORCE_PHASE} — Mandatory Write Artifacts
[lista por fase com paths exatos usando {SYSTEM_DIR}]

## Budget
You have ~{MAX_TURNS} tool turns.

## Prior Phase Context
[injetado pelo script]
```

**REGRA 7.1-7.7:** Template NÃO pede para LLM ler files. Tudo injetado.
**REGRA 7.4:** Declara "under 3000 chars is incomplete".
**REGRA 7.7:** Diz "Do NOT re-read prior outputs".

### Step 3: Gerar Agent Summaries

Para cada agente do pipeline, criar `agents/summaries/{agent}.md` (~2K chars):

```markdown
# {Agent Name} — Agent Summary (for pipeline injection)

**Role:** {tier} — {title}
**Book/Source:** {reference}

## Expertise
- [5-7 bullet points]

## Approach
1. [Numbered steps — how this agent works]

## Expected Outputs
- [What artifacts this agent produces]

## Key Principle
"[One defining quote]"
```

### Step 4: Gerar Python lib/ (se necessário)

Renderizar templates canônicos:
- `pipeline-state-tmpl.py` → `lib/pipeline_state.py`
- `pipeline-progress-tmpl.py` → `lib/progress.py`
- `pipeline-runner-tmpl.py` → `lib/phase_runner.py`

### Step 5: Gerar handler stubs

Criar um stub por fase com assinatura estável.

## Validation

Após render, executar `squads/squad-creator/checklists/pipeline-runner-checklist.md` (30 items).
Score mínimo: 25/30 para PASS.

## Reference Implementations

Ordem de prioridade para consulta:

1. `squads/mmos/scripts/mmos.sh` — **GOLD STANDARD** (task-level granularity, A/B testing, handoff)
2. `squads/domain-decoder/scripts/decoder.sh` — **REFERENCE** (context injection, agent summaries)
3. `squads/books/scripts/books.sh` — 12-phase pipeline
4. `infrastructure/scripts/runner-lib/pipeline-bootstrap.sh` — runner-lib functions

## Post-Mortem Reference

`docs/research/2026-03-31-decoder-pipeline-lessons-learned/` contém:
- 14 bugs catalogados com causa raiz e fix
- 10 princípios para pipelines LLM headless
- Comparação de modelos (haiku vs opus vs sonnet) com dados reais

## Acceptance Criteria

- [ ] `scripts/{squad}.sh` criado, executável
- [ ] `.sh` implementa padrões 1A-1F acima
- [ ] `templates/pipeline/prompt.md` com placeholders de injeção
- [ ] `agents/summaries/*.md` criados para cada agent do pipeline
- [ ] `lib/` renderizado com state manager, phase runner, progress
- [ ] `checklists/pipeline-runner-checklist.md` executado com score ≥ 25/30
- [ ] `bash scripts/{squad}.sh --help` funciona sem erro

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-31_
_Post-mortem: 14 bugs incorporados como regras de geração_
