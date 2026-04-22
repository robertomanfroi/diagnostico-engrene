<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-report
  task_name: Optimize Workflow - Cost Projection & Report
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 20m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Calcular custo atual
  - Calcular custo otimizado
  - Consolidar findings
  - Emitir relatório
  acceptance_criteria:
  - O before/after é calculado com premissas explícitas
  - A projeção final é reutilizável pelo modo --implement
  - O relatório finaliza o modo scan
  - A fila de implementação está ordenada por impacto e risco
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


# Task: Optimize Workflow - Cost Projection & Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-report` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |
| **Merge Note** | Absorveu `optimize-workflow-cost-projection` v1.0.0 |

## Metadata

```yaml
id: optimize-workflow-report
name: "Optimize Workflow Cost Projection & Report"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Calcula custo atual vs. otimizado (D6) e consolida D1-D6 em um relatório de otimização com backlog de implementação."
```

## Purpose

Executar a dimensão D6 (custo) e fechar o modo `--scan` com um artefato único de decisão. Esta task transforma as análises anteriores em métrica de custo, priorização e junta necessidade de fases, paralelização, checkpoints, executor, GAP ZERO e custo.

## Inputs

```yaml
inputs:
  phase_necessity_table:
    type: object
    required: true
  parallel_groups:
    type: object
    required: false
  checkpoint_inventory:
    type: object
    required: false
  executor_distribution_table:
    type: object
    required: false
  gap_findings:
    type: object
    required: false
  cost:
    type: number
    required: false
    default: 10
```

## Workflow / Steps

### Step 1: Calcular custo atual

- Tokens e tempo por execução no estado atual.

### Step 2: Calcular custo otimizado

- Projeção com paralelização e redistribuição de executor.

### Step 3: Consolidar findings

- Unificar D1-D6.
- Priorizar recomendações.

### Step 4: Emitir relatório

- Gerar resumo executivo.
- Gerar fila do que entra em `--implement`.

## Output

```yaml
output:
  schema:
    current_cost: []
    optimized_cost: []
    monthly_projection: []
    optimization_report: []
    implementation_backlog: []
```

## Acceptance Criteria

- [ ] O before/after é calculado com premissas explícitas
- [ ] A projeção final é reutilizável pelo modo `--implement`
- [ ] O relatório finaliza o modo scan
- [ ] A fila de implementação está ordenada por impacto e risco

## Related Documents

- `optimize-workflow.md`
- `optimize-workflow-apply.md`

_Task Version: 2.0.0_
_Merge: optimize-workflow-cost-projection v1.0.0 absorbed into this task_
