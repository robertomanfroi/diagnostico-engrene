<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-empirical-validation
  task_name: Optimize - Empirical Validation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 20m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar superfície otimizada
  - Registrar evidência
  - Rodar alvos contrastantes
  - Detectar e registrar viés
  acceptance_criteria:
  - Toda otimização implementada tem evidência empírica
  - Test case ou payload equivalente é preservado para rerun
  - O teste usa ao menos dois alvos contrastantes quando aplicável
  - Bias findings ficam serializados e reutilizáveis
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


# Task: Optimize - Empirical Validation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-empirical-validation` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: optimize-empirical-validation
name: "Optimize Empirical Validation"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Roda o preflight/script, compara com baseline, salva o teste empírico da task otimizada e executa teste bidirecional de viés."
absorbs:
  - optimize-bias-test
```

## Purpose

Validar empiricamente se a otimização proposta realmente funciona e, em seguida, verificar se ela introduziu viés operacional invisível. Cobre tanto a execução de baseline quanto o teste bidirecional de contraste.

## Inputs

```yaml
inputs:
  gap_zero_patch_plan:
    type: object
    required: true
  target_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Executar superfície otimizada

- Rodar preflight/script do Worker.
- Rodar comparação rápida com baseline quando aplicável.

### Step 2: Registrar evidência

- Salvar test case, resultado e divergências.
- Produzir relatório empírico por target otimizado.

### Step 3: Bias Testing (absorbed from optimize-bias-test)

#### Step 3.1: Rodar alvos contrastantes

- Reexecutar a task otimizada em variações controladas.
- Coletar saídas comparáveis.

#### Step 3.2: Detectar e registrar viés

- Marcar diferença sistemática indevida.
- Salvar bias report para revisão posterior.

## Output

```yaml
output:
  schema:
    empirical_results: []
    saved_test_cases: []
    validation_report: []
    bias_findings: []
    bias_report_paths: []
```

## Acceptance Criteria

- [ ] Toda otimização implementada tem evidência empírica
- [ ] Test case ou payload equivalente é preservado para rerun
- [ ] O teste usa ao menos dois alvos contrastantes quando aplicável
- [ ] Bias findings ficam serializados e reutilizáveis

## Related Documents

- `optimize.md`
- `optimize-post-economy.md`

_Task Version: 2.0.0_
_Absorbs: optimize-bias-test (v1.0.0)_
