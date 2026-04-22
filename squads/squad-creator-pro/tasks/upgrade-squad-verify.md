<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad-verify
  task_name: Upgrade Squad - Verify
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
  - Rodar a verificação estrutural herdada
  - Anexar o residual qualitativo
  acceptance_criteria:
  - A verificação estrutural continua ancorada no task canônico do base
  - Pendências qualitativas não são escondidas nem tratadas como “resolvidas”
  - O report final deixa claro o próximo handoff por item
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


# Task: Upgrade Squad - Verify

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-verify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: upgrade-squad-verify
name: "Upgrade Squad Verify"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Reusa a verificação estrutural do base e separa claramente o que ficou pendente por decisão qualitativa do overlay."
```

## Purpose

Executar a verificação final sem misturar as camadas:
- score e integridade estrutural continuam vindo do base
- pendências qualitativas ficam visíveis como follow-up, não como regressão silenciosa

## Workflow / Steps

### Step 1: Rodar a verificação estrutural herdada

- Ler `squads/squad-creator/tasks/upgrade-squad-verify.md`.
- Recalcular after-score e report estrutural no formato canônico.

### Step 2: Anexar o residual qualitativo

- Separar `remaining_todos.structural` de `remaining_todos.qualitative`.
- Reforçar os handoffs recomendados (`extract-voice-dna`, `extract-thinking-dna`, etc.).

## Output

```yaml
output:
  schema:
    structural_report: {}
    qualitative_followups:
      remaining_todos: []
      handoffs: []
```

## Acceptance Criteria

- [ ] A verificação estrutural continua ancorada no task canônico do base
- [ ] Pendências qualitativas não são escondidas nem tratadas como “resolvidas”
- [ ] O report final deixa claro o próximo handoff por item

## Related Documents

- `squads/squad-creator/tasks/upgrade-squad-verify.md`
- `upgrade-squad.md`
