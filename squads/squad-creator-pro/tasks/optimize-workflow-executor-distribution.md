<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-executor-distribution
  task_name: Optimize Workflow - Executor Distribution
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Carregar o decision tree
  - Classificar fases
  acceptance_criteria:
  - Nenhuma fase é reclassificada por intuição
  - Toda recomendação aponta o porquê do executor sugerido
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Optimize Workflow - Executor Distribution

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-executor-distribution` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-workflow-executor-distribution
name: "Optimize Workflow Executor Distribution"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica o decision tree nas ações de cada fase e propõe redistribuição de executor por fase."
```

## Purpose

Executar a dimensão D4. Esta task identifica onde o workflow ainda está caro ou supercarregado por usar Agent onde deveria usar Worker/Hybrid.

## Inputs

```yaml
inputs:
  workflow_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Carregar o decision tree

- Ler `squads/squad-creator/data/executor-decision-tree.md`.

### Step 2: Classificar fases

- Decompor ações da fase.
- Aplicar Q1-Q6.
- Propor executor final da fase.

## Output

```yaml
output:
  schema:
    executor_distribution_table: []
    worker_or_hybrid_candidates: []
```

## Acceptance Criteria

- [ ] Nenhuma fase é reclassificada por intuição
- [ ] Toda recomendação aponta o porquê do executor sugerido

## Related Documents

- `optimize-workflow.md`
- `squads/squad-creator/data/executor-decision-tree.md`
