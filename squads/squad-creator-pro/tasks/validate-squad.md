<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad
  task_name: Validate Squad (Composed)
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
  - 'Output artifact produced: Location'
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


# Task: Validate Squad (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad` |
| **Version** | `5.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: validate-squad
name: "Validate Squad"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Task composta que orquestra 6 subtasks de validação para squads pro e permanece local como override legítimo do pack."
```

## Purpose

Executar a validação completa de um squad pro em seis etapas, preservando retrocompatibilidade do comando `*validate-squad` e separando claramente gates deterministas, análise semântica, vetos e emissão de relatório.

Ao contrário de outros shadows redundantes do pack, este arquivo **deve permanecer local**: o `squad-creator-pro` usa uma sequência de 6 subtasks e um workflow próprio (`workflows/validate-squad.yaml`) que não equivale ao modelo de 7 etapas do base.

## Execution Sequence

```text
INPUT (squad_name)
  |
[1] validate-squad-deterministic (type-detect + structure + security + coverage)
  |
[2] validate-squad-cross-references
  |
[3] validate-squad-quality
  |
[4] validate-squad-contextual
  |
[5] validate-squad-verdict (veto gates + report)
  |
OUTPUT: Validation report + final score
```

## Sub-Task References

| Sequence | Task ID | File | Type |
|----------|---------|------|------|
| 1 | `validate-squad-deterministic` | `tasks/validate-squad-deterministic.md` | Worker |
| 2 | `validate-squad-cross-references` | `tasks/validate-squad-cross-references.md` | Worker |
| 3 | `validate-squad-quality` | `tasks/validate-squad-quality.md` | Agent |
| 4 | `validate-squad-contextual` | `tasks/validate-squad-contextual.md` | Agent |
| 5 | `validate-squad-verdict` | `tasks/validate-squad-verdict.md` | Worker |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Name of squad to validate |
| `squad_path` | string | No | Override default path |
| `type_override` | string | No | Force detected type |
| `mode` | string | No | `deep` or `quick` |

## Outputs

| Output | Location |
|--------|----------|
| Validation Report | `{squad_path}/docs/validation-report-{date}.md` |
| JSON Report | `{squad_path}/docs/validation-report-{date}.json` |
| Console Summary | stdout |

## Notes

- Este arquivo funciona como stub composto de retrocompatibilidade.
- A lógica detalhada vive nas 5 subtasks (deterministic, cross-references, quality, contextual, verdict).
- v5.0.0: De-atomized 9 subtasks para 6 (type-detect+structure+security+coverage => deterministic, veto+report => verdict).
- O workflow `workflows/validate-squad.yaml` deve referenciar estas subtasks explicitamente.
- Este é um override legítimo do pack, não uma cópia acidental do base.

## Related Documents

| Reference | File |
|-----------|------|
| Workflow | `workflows/validate-squad.yaml` |
| Checklist | `checklists/squad-checklist.md` |
| Type Definitions | `squads/squad-creator/data/squad-type-definitions.yaml` |
| Quality Framework | `data/quality-dimensions-framework.md` |

## Acceptance Criteria

- [ ] Output artifact produced: Location
- [ ] Task output validated against quality standards
