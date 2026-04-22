# Task: Create Pipeline — Design

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline-design` |
| **Version** | `1.1.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-pipeline-design
name: "Create Pipeline — Design"
category: design
agent: squad-chief
elicit: true
autonomous: false
description: "Fecha o contrato de fases, criticalidade, timeout, cache, item_noun e estratégia inline vs handlers."
accountability:
  human: squad-operator
  scope: full
domain: Strategic

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::create_pipeline_design
Output: artifact::create_pipeline_design
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar a decisão de qualificação em um design fechado de pipeline pronto
para renderização determinística.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `pipeline_qualification_contract` | object | Yes | Contrato da fase 1 |
| `phase_definitions` | array | No | Fases já definidas pelo usuário |
| `item_noun` | string | No | Substantivo do item processado |

## Workflow

### Step 1: Fechar fases

Para cada fase, materializar:
- `num`
- `name` em kebab-case
- `critical`
- `timeout_seconds`
- `cacheable`
- `description`

### Step 2: Fechar componentes

Definir TODOS os artefatos a gerar:

**CLI layer (primary — sem isto o pipeline não roda):**
- `scripts/{squad}.sh` — shell runner com runner-lib bootstrap
- `templates/pipeline/prompt.md` — prompt template com placeholders dinâmicos

**Python layer (engine):**
- `lib/pipeline_state.py`, `lib/progress.py`, `lib/phase_runner.py`, `lib/__init__.py`
- `lib/handlers/` (se 5+ fases)

**Context layer (qualidade do output):**
- `agents/summaries/{agent}.md` (~2K chars cada) — 1 por fase com agente externo

### Step 3: Escolher layout

- `< 5` fases -> handlers inline
- `5+` fases -> diretório `handlers/`

### Step 4: Definir contexto por fase

Para cada fase, materializar:
- `agent(s)` → path do summary em `agents/summaries/`
- `task_file(s)` → path do task .md que será injetado inline
- `completion_threshold` → mínimo de chars para aceitar output (3000-4000, NÃO 500)
- `checklist` → path do checklist (se fase de validação)

Definir turn budgets por modelo:
- haiku: 12 turns
- sonnet: 10 turns
- opus: 15 turns

### Step 5: Emitir design

Produzir `pipeline_design_contract` com resumo executivo, listas de fases e
componentes, além do ETA aproximado por item.

## Output

```yaml
pipeline_design_contract:
  squad_name: ""
  item_noun: "items"
  phases: []
  components: []
  handler_layout: "inline|handlers_directory"
  critical_phases: []
  cacheable_phases: []
  # CLI layer (v1.1.0)
  shell_runner: "scripts/{squad}.sh"
  prompt_template: "templates/pipeline/prompt.md"
  agent_summaries: []  # {phase_num, agent_name, summary_path}
  phase_thresholds: {} # {phase_num: min_chars}
  model_turns: {haiku: 12, sonnet: 10, opus: 15}
```

## Acceptance Criteria

- [ ] Todas as fases têm contrato completo (num, name, critical, timeout, cacheable)
- [ ] Componentes a gerar decididos (CLI + Python + Context layers)
- [ ] Layout inline vs handlers decidido
- [ ] Agent summaries definidos para cada fase com agente externo
- [ ] Phase-specific completion thresholds definidos (3000-4000 chars)
- [ ] Model-aware turn budgets definidos (haiku/sonnet/opus)
- [ ] `pipeline_design_contract` emitido com todos os campos

## Related Documents

- `create-pipeline.md`
- `create-pipeline-render.md`
- `templates/pipeline-runner-tmpl.py`

---

_Task Version: 1.1.0_
_Updated: 2026-03-31 — Added CLI layer, agent summaries, phase thresholds, model turns_
