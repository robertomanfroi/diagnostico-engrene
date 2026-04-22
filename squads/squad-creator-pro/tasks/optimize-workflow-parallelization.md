<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-parallelization
  task_name: Optimize Workflow - Parallelization
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
  - Construir o grafo
  - Encontrar oportunidades
  acceptance_criteria:
  - Toda recomendação de paralelização vem com justificativa de dependência
  - Grupos conflitantes ficam explicitamente excluídos
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


# Task: Optimize Workflow - Parallelization

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-parallelization` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-workflow-parallelization
name: "Optimize Workflow Parallelization"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Constrói o grafo de dependências e identifica grupos de fases paralelizáveis sem colidir em recurso ou output."
```

## Purpose

Executar a dimensão D2. Esta task procura economia de tempo sem quebrar dependências reais do workflow.

## Inputs

```yaml
inputs:
  phase_necessity_table:
    type: object
    required: true
```

## Workflow / Steps

### Step 1: Construir o grafo

- Mapear `depends_on`, `produces` e `consumes` por fase.

### Step 2: Encontrar oportunidades

- Sinalizar fases independentes.
- Excluir grupos que competem pelo mesmo agente/recurso.

## Output

```yaml
output:
  schema:
    dependency_graph: []
    parallel_groups: []
    estimated_time_savings: []
```

## Acceptance Criteria

- [ ] Toda recomendação de paralelização vem com justificativa de dependência
- [ ] Grupos conflitantes ficam explicitamente excluídos

## Related Documents

- `optimize-workflow.md`
- `optimize-workflow-checkpoints.md`
