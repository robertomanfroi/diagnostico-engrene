<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-command-sync
  task_name: Squad Fusion - Command Sync
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
  - Sincronizar novos commands
  - Limpar bindings antigos
  acceptance_criteria:
  - O target final fica com commands operacionais [threshold: >= 1]
  - Commands antigos só saem depois da aprovação da fusão [threshold: >= 1]
  - O resultado do sync fica auditável [threshold: >= 1]
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


# Task: Squad Fusion - Command Sync

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-command-sync` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: squad-fusion-command-sync
name: "Squad Fusion Command Sync"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Sincroniza commands do squad fusionado com o ambiente de IDE e remove bindings antigos quando a fusão foi aprovada."
```

## Purpose

Garantir que o squad fusionado fique operacional no ambiente de execução, sem deixar comandos órfãos dos squads anteriores.

## Workflow / Steps

### Step 1: Sincronizar novos commands

- Gerar ou atualizar bindings do target final.
- Garantir que os commands apontem para o squad fusionado.

### Step 2: Limpar bindings antigos

- Remover ou desativar commands obsoletos dos squads fonte quando aplicável.
- Produzir `commands_synced` e `old_commands_removed`.

## Output

```yaml
output:
  schema:
    commands_synced: []
    old_commands_removed: []
```

## Acceptance Criteria

- [ ] O target final fica com commands operacionais [threshold: >= 1]
- [ ] Commands antigos só saem depois da aprovação da fusão [threshold: >= 1]
- [ ] O resultado do sync fica auditável [threshold: >= 1]
