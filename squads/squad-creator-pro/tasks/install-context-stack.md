<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: install-context-stack
  task_name: Install Context Stack (Orchestrator Stub)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Eligibility gate passou (workspace_integration.level >= controlled_runtime_consumer)
  - Audit identificou scripts existentes vs faltantes
  - Domain mapping definiu session schema adaptado ao squad
  - 5 scripts gerados (ou existentes preservados) em `squads/{squad}/scripts/
  - Todos os 5 smoke tests passam (exit code 0)
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Install Context Stack (Orchestrator Stub)

**Task ID:** install-context-stack
**Purpose:** Instalar o stack completo de scripts de contexto em squads com workspace_integration.level >= controlled_runtime_consumer
**Orchestrator:** @squad-chief
**Mode:** Audit + Implementation
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent` (exige leitura estrutural de config, adaptacao de templates e geracao de codigo)
**Model:** `Opus` (REQUIRED)
**Estimated Time:** 1-2h

**Decomposed:** This task was decomposed into 5 atomic sub-tasks. Execute them in sequence.

---

## Sub-Tasks (execute in order)

| # | Task ID | File | Purpose | Est. Time |
|---|---------|------|---------|-----------|
| 1 | ics-audit | `ics-audit.md` | Ler config, verificar eligibility, inventariar scripts | 10-15min |
| 2 | ics-domain-mapping | `ics-domain-mapping.md` | Identificar dominio, mapear paths, definir session schema | 10-15min |
| 3 | ics-generate-scripts | `ics-generate-scripts.md` | Gerar os 5 scripts .cjs adaptados ao dominio | 30-45min |
| 4 | ics-integration | `ics-integration.md` | Registrar scripts no config.yaml e entry agent | 10-15min |
| 5 | ics-validation | `ics-validation.md` | Smoke tests e validacao estrutural | 10-15min |

---

## Command

```text
*install-context-stack {squad_name}
```

Flags:

- `--audit` (default): diagnosticar sem editar
- `--apply`: instalar scripts faltantes
- `--force`: sobrescrever scripts existentes (cria backup timestamped)
- `--agent {id}`: especificar entry agent (default: lido do config.yaml)

Examples:

```text
*install-context-stack aiox-sop
*install-context-stack aiox-sop --apply
*install-context-stack brand --audit
*install-context-stack movement --apply --agent movement-chief
```

---

## Overview

Instala o stack de 5 scripts de contexto que permite a um squad:
1. Centralizar paths de runtime (`runtime-paths.cjs`)
2. Descobrir businesses/products disponiveis (`discover-context.cjs`)
3. Setar sessao ativa (`set-active-context.cjs`)
4. Carregar contexto ativo com readiness (`load-context.cjs`)
5. Mostrar contexto ativo formatado (`show-context.cjs`)

Pre-requisito para greeting deterministico (`create-greeting-script`) e Next Action (`next-action --apply`).

---

## Execution Flow

```
INPUT (squad_name)
    |
[SUB-TASK 1: ics-audit]
    -> Ler config.yaml, verificar eligibility (VETO-CS-001)
    -> Inventariar scripts existentes vs faltantes
    |
[SUB-TASK 2: ics-domain-mapping]
    -> Identificar entidades e paths canonicos
    -> Definir session-context schema
    |
[SUB-TASK 3: ics-generate-scripts]
    -> Gerar 5 scripts adaptados ao dominio
    -> Preservar existentes (VETO-CS-002)
    |
[SUB-TASK 4: ics-integration]
    -> Registrar scripts no config.yaml
    -> Adicionar comandos no entry agent
    |
[SUB-TASK 5: ics-validation]
    -> Smoke test cada script (exit code 0)
    -> Validacao estrutural completa
    |
OUTPUT: 5 scripts + agent atualizado + config atualizado + validation report
```

---

## Veto Conditions (consolidated)

| ID | Condition | Sub-Task |
|----|-----------|----------|
| VETO-CS-001 | Squad sem workspace_integration ou level < controlled_runtime_consumer | ics-audit |
| VETO-CS-002 | Script existente sobrescrito sem backup | ics-generate-scripts |
| VETO-CS-003 | Script gerado depende de estado da LLM | ics-generate-scripts |
| VETO-CS-004 | Session context salvo fora de .aiox/squad-runtime/ | ics-generate-scripts |
| VETO-CS-005 | Script duplica funcionalidade existente | ics-generate-scripts |

---

## Output Contract

```yaml
install_context_stack:
  squad_name: "{squad_name}"
  mode: "audit|apply"
  workspace_level: "{level do config.yaml}"
  scripts_inventory:
    existing: []
    generated: []
    partial: []
  domain_mapping:
    primary_entity: "{entity}"
    session_schema: {}
  integration:
    config_updated: true|false
    agent_updated: true|false
  smoke_tests:
    runtime_paths: "PASS|FAIL"
    discover_context: "PASS|FAIL"
    set_active_context: "PASS|FAIL"
    load_context: "PASS|FAIL"
    show_context: "PASS|FAIL"
  final_result: "PASS|FAIL"
```

---

## Acceptance Criteria

- [ ] Eligibility gate passou (workspace_integration.level >= controlled_runtime_consumer)
- [ ] Audit identificou scripts existentes vs faltantes
- [ ] Domain mapping definiu session schema adaptado ao squad
- [ ] 5 scripts gerados (ou existentes preservados) em `squads/{squad}/scripts/`
- [ ] Todos os 5 smoke tests passam (exit code 0)
- [ ] config.yaml atualizado com secao scripts
- [ ] Entry agent atualizado com comandos *show-context e *set-context
- [ ] Nenhum script existente foi sobrescrito sem avaliacao (VETO-CS-002)

---

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-install-context-stack.yaml`

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `create-greeting-script` |
| **Trigger** | Context stack instalado e validado |
| **Executor** | @squad-chief |

### Handoff Package

- **Scripts gerados:** lista de paths dos 5 scripts
- **Session schema:** campos da sessao ativa deste squad
- **Domain mapping:** entidades primarias e paths canonicos
- **Gaps remanescentes:** scripts parciais que precisam de atencao

---

_Task Version: 2.0.0 (decomposed from v1.0.0)_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-19_
_Decomposed: 2026-03-26_
_Author: squad-chief_

## Task Anatomy

- **Executor:** Agent
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed install-context-stack output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
