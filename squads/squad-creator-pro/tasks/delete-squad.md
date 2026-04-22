<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: delete-squad
  task_name: Delete Squad Artifact Surface
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
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Backup criado e validado
  - Escopo da remoção confirmado explicitamente
  - Journey log e relatório de arquivamento gerados
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Delete Squad Artifact Surface

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `delete-squad` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: delete-squad
name: "Delete Squad Artifact Surface"
category: maintenance
agent: squad-chief
elicit: true
autonomous: false
description: "Executa a retirada controlada de um squad ou artefato do pack, com backup, trilha auditável e atualização do journey log."
task_name: "Delete Squad Artifact Surface"
status: "active"
responsible_executor: "@squad-chief"
execution_type: "Hybrid"
estimated_time: "30-60m"
domain: Tactical
input:
  - "squad_name"
  - "delete_scope"
  - "backup_path"
output:
  - "archive_report"
  - "journey_log_entry"
action_items:
  - "Criar backup verificável da superfície afetada"
  - "Remover ou arquivar apenas os artefatos aprovados"
  - "Atualizar contratos, registries e journey log"
acceptance_criteria:
  - "Backup criado antes de qualquer remoção"
  - "Journey log atualizado com motivo e sucessor quando aplicável"
  - "Nenhum artefato ativo órfão permanece após a remoção"
output_persistence: "transient_output"
accountable_id: "Human:Squad_Operator"
accountability_scope: "full"
escalation_priority: "high"
```

## Purpose

Oferecer um delete contextual para lifecycle do pack sem usar remoção cega. A task existe para cumprir o contrato de lifecycle do validator e para garantir que qualquer retirada seja reversível, auditável e deliberada.

## Command Contract

```text
*delete-squad {squad_name} [--scope artifacts|runtime|full] [--backup-path {path}]
```

## Acceptance Criteria

- [ ] Backup criado e validado
- [ ] Escopo da remoção confirmado explicitamente
- [ ] Journey log e relatório de arquivamento gerados
