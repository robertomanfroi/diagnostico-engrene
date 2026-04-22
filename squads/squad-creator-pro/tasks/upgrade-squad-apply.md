<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad-apply
  task_name: Upgrade Squad - Apply
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Rodar o apply estrutural herdado
  - Mesclar a trilha qualitativa aprovada
  acceptance_criteria:
  - O apply estrutural do base continua intacto
  - Todo patch qualitativo aplicado veio de plano aprovado
  - TODOs e handoffs diferidos ficam registrados no log final
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Upgrade Squad - Apply

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-apply` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: upgrade-squad-apply
name: "Upgrade Squad Apply"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Executa primeiro o apply estrutural herdado do base e depois incorpora apenas os patches qualitativos aprovados ou placeholders explícitos."
```

## Purpose

Aplicar o plano aprovado sem duplicar a lógica do base:
- estrutural -> usar o baseline de `squads/squad-creator/tasks/upgrade-squad-apply.md`
- qualitativo -> aplicar somente o que veio em `apply_now` ou inserir TODO/handoff explícito

## Workflow / Steps

### Step 1: Rodar o apply estrutural herdado

- Ler `squads/squad-creator/tasks/upgrade-squad-apply.md`.
- Preservar `backup`, `dry-run`, validação por arquivo e `upgrade_log`.

### Step 2: Mesclar a trilha qualitativa aprovada

- Aplicar apenas patches marcados como `apply_now`.
- Inserir TODOs/handoffs onde o plano qualitativo mandou adiar.
- Nunca eliminar o backup/restore do baseline estrutural.

## Output

```yaml
output:
  schema:
    upgrade_log: {}
    qualitative_applied: []
    qualitative_deferred: []
```

## Acceptance Criteria

- [ ] O apply estrutural do base continua intacto
- [ ] Todo patch qualitativo aplicado veio de plano aprovado
- [ ] TODOs e handoffs diferidos ficam registrados no log final

## Related Documents

- `squads/squad-creator/tasks/upgrade-squad-apply.md`
- `upgrade-squad-verify.md`
