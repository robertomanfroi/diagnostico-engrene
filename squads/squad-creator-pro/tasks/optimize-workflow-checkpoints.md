<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-checkpoints
  task_name: Optimize Workflow - Checkpoints
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
  - Inventariar checkpoints
  - Classificar
  acceptance_criteria:
  - Todo checkpoint encontrado recebe destino explícito
  - Gates humanos críticos são preservados
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


# Task: Optimize Workflow - Checkpoints

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-checkpoints` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-workflow-checkpoints
name: "Optimize Workflow Checkpoints"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Inventaria checkpoints, distingue gates humanos legítimos de gates heurísticos e produz plano de conversão."
```

## Purpose

Executar a dimensão D3. Esta task reduz checkpoints humanos desnecessários sem remover gates críticos.

## Inputs

```yaml
inputs:
  workflow_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Inventariar checkpoints

- Localizar `checkpoint`, `approval_required`, `human_review`, `gate`.

### Step 2: Classificar

- `KEEP_HUMAN`
- `HEURISTIC_CANDIDATE`
- `REMOVE_IF_REDUNDANT`

## Output

```yaml
output:
  schema:
    checkpoint_inventory: []
    heuristic_conversion_candidates: []
    human_gate_exceptions: []
```

## Acceptance Criteria

- [ ] Todo checkpoint encontrado recebe destino explícito
- [ ] Gates humanos críticos são preservados

## Related Documents

- `optimize-workflow.md`
- `checklists/quality-gate-checklist.md`
