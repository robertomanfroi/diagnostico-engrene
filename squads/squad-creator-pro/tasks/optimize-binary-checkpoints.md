<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-binary-checkpoints
  task_name: Optimize - Binary Checkpoints
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
  - Detectar scoring subjetivo
  - Converter para binário
  - Adicionar calibração mínima
  acceptance_criteria:
  - Os candidatos binários viram critérios mensuráveis
  - O patch plan preserva gates humanos legítimos
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


# Task: Optimize - Binary Checkpoints

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-binary-checkpoints` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-binary-checkpoints
name: "Optimize Binary Checkpoints"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Converte scoring subjetivo em checkpoints binários, thresholds e critérios calibrados."
```

## Purpose

Reduzir subjetividade operacional antes de qualquer migração de executor. Esta task ataca a parte do monólito focada em scores vagos, gates interpretativos e calibração mínima.

## Inputs

```yaml
inputs:
  binary_conversion_candidates:
    type: object
    required: true
  target_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Detectar scoring subjetivo

- Localizar `1-5`, `rate`, `avalie`, `score` sem threshold operacional.

### Step 2: Converter para binário

- Trocar julgamento vago por PASS/FAIL, YES/NO ou threshold mensurável.

### Step 3: Adicionar calibração mínima

- Registrar regra de decisão e fallback quando o critério falhar.

## Output

```yaml
output:
  schema:
    checkpoint_patch_plan: []
    calibrated_thresholds: []
```

## Acceptance Criteria

- [ ] Os candidatos binários viram critérios mensuráveis
- [ ] O patch plan preserva gates humanos legítimos

## Related Documents

- `optimize.md`
- `optimize-gatekeeper-detection.md`
- `checklists/quality-gate-checklist.md`
