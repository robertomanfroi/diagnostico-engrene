<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad-qualitative
  task_name: Upgrade Squad - Qualitative Remediation
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
  - Classificar cada gap qualitativo
  - Emitir patch plan qualitativo
  acceptance_criteria:
  - Nenhum conteúdo qualitativo é inventado sem evidência
  - Todo item pendente vira handoff ou TODO explícito
  - O output é consumível por `upgrade-squad-apply
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


# Task: Upgrade Squad - Qualitative Remediation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-qualitative` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: upgrade-squad-qualitative
name: "Upgrade Squad Qualitative Remediation"
category: upgrade
agent: squad-chief
elicit: true
autonomous: false
description: "Resolve a trilha qualitativa do upgrade sem inventar conteúdo: aplica com evidência, delega pesquisa ou marca TODO explícito."
```

## Purpose

Materializar somente a parte qualitativa do plano pro: conteúdo de `voice_dna`, `output_examples`, `objection_algorithms`, routing avançado e sinais de governança que dependem de contexto real.

## Workflow / Steps

### Step 1: Classificar cada gap qualitativo

- `apply_now`: há evidência concreta no próprio squad ou em artefatos de suporte.
- `delegate_research`: falta evidência e o caso pede pesquisa.
- `mark_todo`: o item é legítimo, mas não deve ser inventado automaticamente.

### Step 2: Emitir patch plan qualitativo

- Para `apply_now`, preparar mudanças específicas por arquivo.
- Para `delegate_research`, apontar o handoff exato.
- Para `mark_todo`, registrar placeholders e instruções claras no report final.

## Output

```yaml
output:
  schema:
    qualitative_actions:
      apply_now: []
      delegate_research: []
      mark_todo: []
```

## Acceptance Criteria

- [ ] Nenhum conteúdo qualitativo é inventado sem evidência
- [ ] Todo item pendente vira handoff ou TODO explícito
- [ ] O output é consumível por `upgrade-squad-apply`

## Related Documents

- `upgrade-squad-plan.md`
- `upgrade-squad-apply.md`
