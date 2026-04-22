<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-phase-necessity
  task_name: Optimize Workflow - Load & Phase Necessity
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
  - Resolver target
  - Carregar e validar
  - Decompor fases
  - Classificar contribuição
  acceptance_criteria:
  - O alvo é resolvido sem ambiguidade
  - Workflows inválidos são bloqueados antes da análise
  - Cada fase recebe classificação objetiva
  - O output diferencia remoção de merge
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
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Optimize Workflow - Load & Phase Necessity

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-phase-necessity` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |
| **Merge Note** | Absorveu `optimize-workflow-load` v1.0.0 |

## Metadata

```yaml
id: optimize-workflow-phase-necessity
name: "Optimize Workflow Load & Phase Necessity"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Resolve o target, carrega e valida workflows, depois classifica fases como essential, redundant ou merge_candidate com base em output único, impacto de remoção e consumo downstream."
```

## Purpose

Resolver `target`, produzir o inventário factual dos workflows a otimizar e executar a dimensão D1 (necessidade de fases). Esta task impede otimização sobre YAML inválido ou alvo ambíguo e mede quanto do workflow é realmente necessário antes de qualquer paralelização ou refactor.

## Inputs

```yaml
inputs:
  target:
    type: string
    required: true
  mode:
    type: string
    required: false
    default: scan
```

## Workflow / Steps

### Step 1: Resolver target

- Se `target` for arquivo, operar em um workflow.
- Se `target` for nome de squad, listar `workflows/*.yaml` do squad.

### Step 2: Carregar e validar

- Ler cada workflow por completo.
- Confirmar `workflow.id` e `sequence` ou estrutura equivalente.
- Registrar necessidade de backup para `--implement`.

### Step 3: Decompor fases

- Extrair nome, propósito, inputs, outputs, dependências e agente por fase.

### Step 4: Classificar contribuição

- `ESSENTIAL`: output único e necessário.
- `REDUNDANT`: não produz output útil nem quebra o fluxo.
- `MERGE_CANDIDATE`: agrega pouco e pode ser absorvida por outra fase.

## Output

```yaml
output:
  schema:
    resolved_scope: "single-workflow | squad"
    workflow_files: []
    structure_valid: true
    backups_required: true
    phase_necessity_table: []
    redundant_candidates: []
    merge_candidates: []
```

## Acceptance Criteria

- [ ] O alvo é resolvido sem ambiguidade
- [ ] Workflows inválidos são bloqueados antes da análise
- [ ] Cada fase recebe classificação objetiva
- [ ] O output diferencia remoção de merge

## Related Documents

- `optimize-workflow.md`
- `optimize-workflow-parallelization.md`

_Task Version: 2.0.0_
_Merge: optimize-workflow-load v1.0.0 absorbed into this task_
