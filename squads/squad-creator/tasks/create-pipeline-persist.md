# Task: Create Pipeline — Persist

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline-persist` |
| **Version** | `1.1.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-pipeline-persist
name: "Create Pipeline — Persist"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Persiste o bundle renderizado completo: scripts/{squad}.sh, templates/pipeline/prompt.md, agents/summaries/, lib/ e handlers."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_pipeline_persist
Output: artifact::create_pipeline_persist
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Salvar o bundle renderizado no squad alvo sem reinventar estrutura ou layout.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `pipeline_design_contract` | object | Yes | Contrato de design |
| `pipeline_render_bundle` | object | Yes | Bundle renderizado |

## Workflow

### Step 1: Garantir layout

Criar TODOS os diretórios necessários:
- `scripts/` — shell runner
- `templates/pipeline/` — prompt template
- `agents/summaries/` — agent summaries para injeção
- `lib/` — Python engine
- `lib/handlers/` — quando layout exigir (5+ fases)

### Step 2: Persistir CLI layer (PRIMARY)

- `scripts/{squad}.sh` — chmod +x obrigatório
- `templates/pipeline/prompt.md` — prompt com placeholders dinâmicos

### Step 3: Persistir context layer

- `agents/summaries/{agent}.md` — 1 por fase com agente externo (~2K chars cada)

### Step 4: Persistir Python layer

Salvar `lib/pipeline_state.py`, `lib/progress.py`, `lib/phase_runner.py`, `lib/__init__.py`
e arquivos de handler quando necessário.

### Step 5: Emitir relatório de persistência

Registrar paths escritos e eventuais sobrescritas controladas.

## Acceptance Criteria

- [ ] `scripts/{squad}.sh` persistido e executável (chmod +x)
- [ ] `templates/pipeline/prompt.md` persistido
- [ ] `agents/summaries/` persistido com 1+ arquivos
- [ ] `lib/` criado com pipeline_state.py, phase_runner.py, progress.py, __init__.py
- [ ] `lib/handlers/` criado quando necessário (5+ fases)
- [ ] Relatório de persistência emitido com todos os paths

## Related Documents

- `create-pipeline.md`
- `create-pipeline-validate.md`
- `templates/pipeline-runner-tmpl.py`

---

_Task Version: 1.1.0_
_Updated: 2026-03-31 — Added CLI layer (scripts/, templates/pipeline/) and context layer (agents/summaries/)_
