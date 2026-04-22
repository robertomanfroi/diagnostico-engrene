<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-discovery
  task_name: Squad Fusion - Discovery
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Inventariar cada fonte
  - Consolidar visão global
  acceptance_criteria:
  - Todos os squads fonte entram no inventário [threshold: >= 1]
  - O inventário cobre assets e referências cruzadas [threshold: >= 1]
  - O output é suficiente para deduplicação e filtragem [threshold: score >= 0.8]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
  coherence_threshold: 0.95
  error_behavior: raise
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Squad Fusion - Discovery

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-discovery` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: squad-fusion-discovery
name: "Squad Fusion Discovery"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Faz due diligence dos squads fonte, inventariando assets, contagens e referências cruzadas antes da deduplicação."
```

## Purpose

Produzir um inventário factual dos squads fonte para que nenhuma decisão de fusão dependa de memória ou suposição.

## Workflow / Steps

### Step 1: Inventariar cada fonte

- Listar agents, tasks, workflows, templates, checklists, data, scripts e config.
- Contar linhas e metadados mínimos por arquivo.

### Step 2: Consolidar visão global

- Produzir `inventory`, `total_assets` e `cross_references`.
- Destacar dependências cruzadas que precisam sobreviver à fusão.

## Output

```yaml
output:
  schema:
    inventory: {}
    total_assets: {}
    cross_references: []
```

## Acceptance Criteria

- [ ] Todos os squads fonte entram no inventário [threshold: >= 1]
- [ ] O inventário cobre assets e referências cruzadas [threshold: >= 1]
- [ ] O output é suficiente para deduplicação e filtragem [threshold: score >= 0.8]
