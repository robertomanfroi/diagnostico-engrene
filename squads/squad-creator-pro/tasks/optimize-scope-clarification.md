<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-scope-clarification
  task_name: Optimize - Scope Clarification
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
  - Detectar ambiguidade
  - Propor escopo explícito
  acceptance_criteria:
  - Toda ambiguidade material é identificada
  - O plano resultante pode ser aplicado sem reinterpretar a intenção depois
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


# Task: Optimize - Scope Clarification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-scope-clarification` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-scope-clarification
name: "Optimize Scope Clarification"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Detecta tasks com escopo ambíguo e propõe contratos de arquivo, alvo e saída explícitos antes de qualquer conversão."
```

## Purpose

Eliminar ambiguidade operacional que distorce a comparação entre modelos e degrada ROI. Esta task é o gate que separa problema de executor de problema de escopo.

## Inputs

```yaml
inputs:
  analysis_table:
    type: object
    required: true
  target_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Detectar ambiguidade

- Localizar paths dinâmicos, placeholders amplos e targets implícitos.
- Marcar tasks que misturam múltiplos artefatos sem lista fechada.

### Step 2: Propor escopo explícito

- Definir arquivo(s) alvo, tipo de output e limites do que pode ser alterado.
- Preparar patch plan de escopo, sem ainda reescrever a task.

## Output

```yaml
output:
  schema:
    ambiguous_tasks: []
    scope_patch_plan: []
```

## Acceptance Criteria

- [ ] Toda ambiguidade material é identificada
- [ ] O plano resultante pode ser aplicado sem reinterpretar a intenção depois

## Related Documents

- `optimize.md`
- `optimize-gatekeeper-detection.md`
