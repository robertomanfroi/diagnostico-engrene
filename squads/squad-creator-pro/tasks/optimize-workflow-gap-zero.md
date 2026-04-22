<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-gap-zero
  task_name: Optimize Workflow - Gap Zero
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
  - Mapear handoffs
  - Detectar gaps
  acceptance_criteria:
  - Todo gap encontrado tem ação corretiva proposta
  - Handoffs críticos ficam rastreáveis
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


# Task: Optimize Workflow - Gap Zero

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-gap-zero` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-workflow-gap-zero
name: "Optimize Workflow Gap Zero"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Mapeia handoffs, detecta gaps entre fases e propõe correções para eliminar idle time e dependências implícitas."
```

## Purpose

Executar a dimensão D5. Esta task ataca handoffs frágeis, gaps de contexto e transições sem contrato explícito.

## Inputs

```yaml
inputs:
  dependency_graph:
    type: object
    required: true
  workflow_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Mapear handoffs

- Quem produz
- Quem consome
- Que artefato cruza a transição

### Step 2: Detectar gaps

- Output não consumido
- Input não declarado
- Transição com espera desnecessária

## Output

```yaml
output:
  schema:
    handoff_map: []
    gap_findings: []
    gap_zero_patch_plan: []
```

## Acceptance Criteria

- [ ] Todo gap encontrado tem ação corretiva proposta
- [ ] Handoffs críticos ficam rastreáveis

## Related Documents

- `optimize-workflow.md`
- `optimize-workflow-report.md`
