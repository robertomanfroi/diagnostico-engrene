<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-gatekeeper-detection
  task_name: Optimize - Gatekeeper Detection
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
  - Detectar gatekeepers
  - Qualificar o gate
  acceptance_criteria:
  - Todo gate identificado tem rationale
  - Candidatos a conversão binária ficam separados de gates humanos legítimos
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


# Task: Optimize - Gatekeeper Detection

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-gatekeeper-detection` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-gatekeeper-detection
name: "Optimize Gatekeeper Detection"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Detecta padroes de gatekeeper, checkpoints subjetivos e dependencias humanas mal posicionadas antes da implementacao."
```

## Purpose

Separar o que é validação legítima do que é gargalo humano desnecessário. Esta task governa conversões de checkpoint e impede automação insegura.

## Inputs

```yaml
inputs:
  analysis_table:
    type: object
    required: true
  scope_patch_plan:
    type: object
    required: false
```

## Workflow / Steps

### Step 1: Detectar gatekeepers

- Procurar scores subjetivos, checkpoints vagos e aprovações humanas sem threshold.
- Identificar where a human gate is structural versus accidental.

### Step 2: Qualificar o gate

- Manter gates realmente críticos.
- Marcar gates convertíveis para binário ou heurístico.
- Preparar lista de conversão para as phases seguintes.

## Output

```yaml
output:
  schema:
    gatekeeper_findings: []
    binary_conversion_candidates: []
    human_gate_exceptions: []
```

## Acceptance Criteria

- [ ] Todo gate identificado tem rationale
- [ ] Candidatos a conversão binária ficam separados de gates humanos legítimos

## Related Documents

- `optimize.md`
- `optimize-binary-checkpoints.md`
- `checklists/quality-gate-checklist.md`
