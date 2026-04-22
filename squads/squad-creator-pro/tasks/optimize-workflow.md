<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow
  task_name: Optimize Workflow Execution (Composed)
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
  - '*optimize-workflow` continua compatível para os chamadores atuais'
  - A lógica detalhada sai do monólito e vai para tasks atômicas
  - O fluxo canônico do pack fica explicitado em `wf-optimize-workflow.yaml
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


# Task: Optimize Workflow Execution (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow` |
| **Version** | `3.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: optimize-workflow
name: "Optimize Workflow Execution"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Stub composto que preserva o entrypoint *optimize-workflow e delega a análise e implementação ao workflow canônico do pack."
```

## Purpose

Preservar compatibilidade do comando `*optimize-workflow` e dos chamadores internos do pack enquanto a lógica detalhada passa a viver em tasks atômicas orquestradas por workflow dedicado.

## Canonical Owner

- `workflows/wf-optimize-workflow.yaml` é o owner canônico do fluxo de otimização de workflows no `squad-creator-pro`.

## Command Contract

```text
*optimize-workflow {target}

Flags:
--scan        Executa apenas análise
--implement   Aplica as otimizações aprovadas
--cost N      Ajusta a projeção mensal
--verbose     Amplia o relatório por fase
```

## Execution Sequence

| Sequence | Task ID | File | Type |
|----------|---------|------|------|
| 1 | `optimize-workflow-phase-necessity` | `tasks/optimize-workflow-phase-necessity.md` | Agent |
| 2 | `optimize-workflow-parallelization` | `tasks/optimize-workflow-parallelization.md` | Agent |
| 3 | `optimize-workflow-checkpoints` | `tasks/optimize-workflow-checkpoints.md` | Agent |
| 4 | `optimize-workflow-executor-distribution` | `tasks/optimize-workflow-executor-distribution.md` | Agent |
| 5 | `optimize-workflow-gap-zero` | `tasks/optimize-workflow-gap-zero.md` | Agent |
| 6 | `optimize-workflow-report` | `tasks/optimize-workflow-report.md` | Worker |
| 7 | `optimize-workflow-apply` | `tasks/optimize-workflow-apply.md` | Agent |

## Mode Map

```yaml
mode_map:
  scan:
    run:
      - optimize-workflow-phase-necessity
      - optimize-workflow-parallelization
      - optimize-workflow-checkpoints
      - optimize-workflow-executor-distribution
      - optimize-workflow-gap-zero
      - optimize-workflow-report
  implement:
    run:
      - optimize-workflow-phase-necessity
      - optimize-workflow-parallelization
      - optimize-workflow-checkpoints
      - optimize-workflow-executor-distribution
      - optimize-workflow-gap-zero
      - optimize-workflow-report
      - optimize-workflow-apply
```

## Veto Conditions

- Não aplicar `--implement` sem backup
- Não aplicar `--implement` sem relatório de scan
- Não fechar a execução sem validação estrutural do YAML final

## Acceptance Criteria

- [ ] `*optimize-workflow` continua compatível para os chamadores atuais
- [ ] A lógica detalhada sai do monólito e vai para tasks atômicas
- [ ] O fluxo canônico do pack fica explicitado em `wf-optimize-workflow.yaml`

## Related Documents

- `workflows/wf-optimize-workflow.yaml`
- `tasks/optimize.md`
- `workflows/wf-optimize-squad.yaml`

_Task Version: 3.0.0_
_De-atomization: 10 subtasks consolidated to 7 (load merged into phase-necessity, cost-projection merged into report, validate merged into apply)_
