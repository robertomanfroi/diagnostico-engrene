<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion
  task_name: Squad Fusion (Composed)
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
  - All veto conditions checked and none triggered
  - 'Output artifact produced: Completed squad-fusion output artifact'
  - Task output validated against quality standards
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


# Task: Squad Fusion (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: squad-fusion
name: "Squad Fusion"
category: fusion
agent: squad-chief
elicit: true
autonomous: false
description: "Stub composto que preserva o entrypoint *squad-fusion e delega a execução real para o workflow canônico de fusão do pack pro."
```

## Purpose

Preservar o comando `*squad-fusion` sem manter o monólito anterior. A lógica real passa a viver em tasks atômicas ligadas ao `wf-squad-fusion.yaml`, que continua sendo o owner canônico do processo de fusão.

## Canonical Owner

- `workflows/wf-squad-fusion.yaml` é o owner canônico de `*squad-fusion`.

## Command Contract

```text
*squad-fusion

Flags:
--sources a,b,c
--target target-name
--mode yolo|quality
--dry-run
--keep-sources
--verbose
```

## Execution Sequence

| Seq | Task ID | File | Type | Phase |
|-----|---------|------|------|-------|
| 1 | `squad-fusion-initialize` | `tasks/squad-fusion-initialize.md` | Hybrid | Setup (elicit + init) |
| 2 | `squad-fusion-discovery` | `tasks/squad-fusion-discovery.md` | Worker | Discovery |
| 3 | `squad-fusion-deduplication` | `tasks/squad-fusion-deduplication.md` | Agent | Dedup + Analysis |
| 4 | `squad-fusion-scope` | `tasks/squad-fusion-scope.md` | Agent | Scope |
| 5 | `squad-fusion-resolution` | `tasks/squad-fusion-resolution.md` | Hybrid | Resolution |
| 6 | `squad-fusion-execution` | `tasks/squad-fusion-execution.md` | Worker | Execution |
| 7 | `squad-fusion-validation` | `tasks/squad-fusion-validation.md` | Hybrid | Validation |
| 8 | `squad-fusion-structure` | `tasks/squad-fusion-structure.md` | Worker | Structure (collect + materialize) |
| 9 | `squad-fusion-integration` | `tasks/squad-fusion-integration.md` | Hybrid | Integration |
| 10 | `squad-fusion-command-sync` | `tasks/squad-fusion-command-sync.md` | Worker | Cmd Sync |
| 11 | `squad-fusion-cleanup` | `tasks/squad-fusion-cleanup.md` | Human | Cleanup |

## Mode Map

```yaml
mode_map:
  dry_run:
    run: [seq 1-4]  # Stops after scope -- no writes
  yolo:
    run: [seq 1-10] # Automatic checkpoints
  quality:
    run: [seq 1-10] # Human checkpoints at hybrid/human phases
```

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-SFU-001 | Fewer than 2 valid source squads | BLOCK |
| VETO-SFU-002 | No dry-run analysis before destructive merge | BLOCK |
| VETO-SFU-003 | No rollback path before writing | BLOCK |
| VETO-SFU-004 | Cleanup without quality gates pass | BLOCK |

## Quality Gates

| Gate ID | Name | Type |
|---------|------|------|
| SC_FUS_001 | Fusion Completeness | Blocking |
| SC_FUS_002 | Config Validity | Blocking |
| SC_FUS_003 | Documentation Quality | Recommended |

## Related Documents

- `workflows/wf-squad-fusion.yaml`
- `data/fusion-decision-points-analysis.md`
- `data/fusion-executor-analysis.md`
- `checklists/executor-matrix-checklist.md`
- `templates/config-tmpl.yaml`
- `templates/readme-tmpl.md`

_Task Version: 2.0.0_
_Role: composed stub orchestrating 10 fusion sub-tasks (de-atomized from 14)_

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Completed squad-fusion output artifact
- [ ] Task output validated against quality standards
