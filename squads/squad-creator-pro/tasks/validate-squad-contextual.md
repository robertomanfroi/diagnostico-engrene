<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad-contextual
  task_name: Validate Squad - Contextual
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
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - O output muda conforme o tipo detectado
  - O score e calculado com criterios especificos do tipo
  - Issues mostram o gap contextual real do squad
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


# Task: Validate Squad - Contextual

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-contextual` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: validate-squad-contextual
name: "Validate Squad Contextual"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica validacao especifica ao tipo detectado do squad: expert, pipeline ou hybrid."
```

## Purpose

Avaliar se o squad e bom para o tipo de sistema que ele afirma ser. Nao existe validacao unica para todos os perfis.

## Inputs

```yaml
inputs:
  detected_type:
    type: string
    required: true
  squad_name:
    type: string
    required: true
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
```

## Workflow / Steps

### Expert

- Validar `voice_dna`, exemplos, objecoes e organizacao por tiers.

### Pipeline

- Validar definicao de workflow, checkpoints, outputs intermediarios e completude do orquestrador.

### Hybrid

- Validar `behavioral_states`, heuristicas, process standards e modelo de executor/fallback.

## Output

```yaml
output:
  schema:
    squad_type: "expert | pipeline | hybrid"
    score: 0.0
    checks: {}
    issues: []
```

## Acceptance Criteria

- [ ] O output muda conforme o tipo detectado
- [ ] O score e calculado com criterios especificos do tipo
- [ ] Issues mostram o gap contextual real do squad

## Related Documents

- `validate-squad.md`
- `validate-squad-deterministic.md`
- `validate-squad-verdict.md`
