<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize
  task_name: Optimize Squad/Task Execution (Composed)
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
  - '*optimize` continua compatível para chamadores atuais'
  - O modo de execução escolhe o subconjunto correto de subtasks
  - A implementação detalhada foi movida para tasks atômicas
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: Optimize Squad/Task Execution (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize` |
| **Version** | `6.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: optimize
name: "Optimize Squad/Task Execution"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Stub composto que preserva o entrypoint *optimize e orquestra as 8 subtasks atomicas de analise, conversao, validacao e economia."
```

## Purpose

Preservar retrocompatibilidade do comando `*optimize` enquanto a lógica real passa a viver em subtasks especializadas. Este arquivo continua sendo o owner do entrypoint, mas não volta a concentrar a implementação inteira.

## Command Contract

```text
*optimize {target}

Flags:
--scan        Executa apenas análise e relatório inicial
--implement   Executa análise + conversões estruturais
--hybrid      Executa o pipeline completo até validação empírica
--post        Recalcula economia a partir de artefatos já gerados
--exec N      Ajusta projeção de economia
```

## Mode Map

```yaml
mode_map:
  scan:
    run:
      - optimize-determinism-analysis
      - optimize-scope-clarification
      - optimize-gatekeeper-detection
      - optimize-post-economy
  implement:
    run:
      - optimize-determinism-analysis
      - optimize-scope-clarification
      - optimize-gatekeeper-detection
      - optimize-post-economy
      - optimize-binary-checkpoints
      - optimize-hybrid-executor
      - optimize-gap-zero
  hybrid:
    run:
      - optimize-determinism-analysis
      - optimize-scope-clarification
      - optimize-gatekeeper-detection
      - optimize-binary-checkpoints
      - optimize-hybrid-executor
      - optimize-gap-zero
      - optimize-empirical-validation
      - optimize-post-economy
  post:
    run:
      - optimize-post-economy
```

## Execution Sequence

| Sequence | Task ID | File | Type |
|----------|---------|------|------|
| 1 | `optimize-determinism-analysis` | `tasks/optimize-determinism-analysis.md` | Agent |
| 2 | `optimize-scope-clarification` | `tasks/optimize-scope-clarification.md` | Agent |
| 3 | `optimize-gatekeeper-detection` | `tasks/optimize-gatekeeper-detection.md` | Agent |
| 4 | `optimize-binary-checkpoints` | `tasks/optimize-binary-checkpoints.md` | Agent |
| 5 | `optimize-hybrid-executor` | `tasks/optimize-hybrid-executor.md` | Agent |
| 6 | `optimize-gap-zero` | `tasks/optimize-gap-zero.md` | Agent |
| 7 | `optimize-empirical-validation` | `tasks/optimize-empirical-validation.md` | Worker |
| 8 | `optimize-post-economy` | `tasks/optimize-post-economy.md` | Worker |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `target` | string | Yes | Task file, squad name ou `all` |
| `mode` | string | No | `scan`, `implement`, `hybrid` ou `post` |
| `exec` | number | No | Volume de execuções para projeção |

## Outputs

| Output | Description |
|--------|-------------|
| Determinism Analysis | Análise Q1-Q6 por task e por ação |
| ROI Report | Matriz de prioridade e economia projetada |
| Patch Plans | Conversões binárias, hybrid e GAP ZERO |
| Final Economy Report | Before/after consolidado |

## Veto Conditions

- Não iniciar classificação sem ler `squads/squad-creator/data/executor-decision-tree.md`
- Não propor mudança destrutiva em `--implement` ou `--hybrid` sem backup requirement explícito
- Não fechar `--hybrid` sem validação empírica e bias test

## Notes

- `wf-optimize-squad.yaml` passa a compor estas subtasks com `task_ref`.
- `wf-optimize-yolo.yaml` continua owner do ciclo autônomo de alto nível e pode reutilizar estas mesmas subtasks por referência.
- Este arquivo substitui o monólito anterior por contrato de composição.
- De-atomization v6.0.0: 11 subtasks consolidadas em 8 (target-inventory absorbed by determinism-analysis, bias-test absorbed by empirical-validation, roi-report absorbed by post-economy).

## Acceptance Criteria

- [ ] `*optimize` continua compatível para chamadores atuais
- [ ] O modo de execução escolhe o subconjunto correto de subtasks
- [ ] A implementação detalhada foi movida para tasks atômicas

## Related Documents

- `workflows/wf-optimize-squad.yaml`
- `workflows/wf-optimize-yolo.yaml`
- `checklists/quality-gate-checklist.md`

_Task Version: 6.0.0_
_Role: compatibility stub for atomic optimization pipeline (8 subtasks)_
