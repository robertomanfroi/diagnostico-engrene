<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad-cross-references
  task_name: Validate Squad - Cross References
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
  - Handoffs
  - Task references
  - Template e checklist references
  acceptance_criteria:
  - Handoffs quebrados bloqueiam a validacao
  - Task refs invalidos sao listados com path ou id
  - Templates/checklists ausentes ficam visiveis no output
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


# Task: Validate Squad - Cross References

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-cross-references` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: validate-squad-cross-references
name: "Validate Squad Cross References"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Valida handoffs, referencias de tasks, templates e checklists para impedir links quebrados ou dependencias fantasma."
```

## Purpose

Garantir que as referencias internas do squad apontem para artefatos reais e coerentes. Esta task protege contra drift estrutural silencioso.

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
```

## Workflow / Steps

### Step 1: Handoffs

- Verificar se todos os `handoff_to` apontam para agentes existentes.

### Step 2: Task references

- Verificar se tasks referenciadas em workflows, agentes ou docs operacionais existem.

### Step 3: Template e checklist references

- Verificar paths de templates e checklists citados nas tasks.
- Tratar ausencias como warning quando nao forem gates bloqueantes.

## Output

```yaml
output:
  schema:
    status: "PASS | ABORT | WARN"
    broken_handoffs: 0
    broken_task_refs: []
    missing_templates: []
    missing_checklists: []
```

## Acceptance Criteria

- [ ] Handoffs quebrados bloqueiam a validacao
- [ ] Task refs invalidos sao listados com path ou id
- [ ] Templates/checklists ausentes ficam visiveis no output

## Related Documents

- `validate-squad.md`
- `validate-squad-deterministic.md`
