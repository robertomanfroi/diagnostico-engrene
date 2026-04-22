<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-gap-zero
  task_name: Optimize - Gap Zero
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
  - Inserir blocos de execução
  - Adicionar vetos e versão
  acceptance_criteria:
  - Nenhum preflight mandatório fica implícito
  - Os vetos necessários ficam materializados antes da validação empírica
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


# Task: Optimize - Gap Zero

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-gap-zero` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-gap-zero
name: "Optimize Gap Zero"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica EXECUTE FIRST, INPUT REQUIRED e vetos estruturais para eliminar gaps entre handoff e execução."
```

## Purpose

Garantir que a task otimizada já nasça operacionalmente fechada. Esta task cuida da parte de GAP ZERO do monólito original.

## Inputs

```yaml
inputs:
  worker_conversion_plan:
    type: object
    required: true
  backup_requirements:
    type: object
    required: false
```

## Workflow / Steps

### Step 1: Inserir blocos de execução

- Adicionar `EXECUTE FIRST` quando houver preflight obrigatório.
- Declarar `INPUT REQUIRED` quando o output de script for insumo mandatório.

### Step 2: Adicionar vetos e versão

- Registrar veto conditions necessárias.
- Atualizar versão da task quando a conversão alterar o contrato.

## Output

```yaml
output:
  schema:
    gap_zero_patch_plan: []
    added_vetos: []
    version_updates: []
```

## Acceptance Criteria

- [ ] Nenhum preflight mandatório fica implícito
- [ ] Os vetos necessários ficam materializados antes da validação empírica

## Related Documents

- `optimize.md`
- `optimize-empirical-validation.md`
