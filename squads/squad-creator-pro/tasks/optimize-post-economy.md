<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-post-economy
  task_name: Optimize - Post Economy
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
  - Estimar custo e ganho
  - Priorizar
  - Emitir relatório ROI
  - Inventariar mudanças
  - Calcular economia
  - Emitir relatório final
  acceptance_criteria:
  - O relatório ROI finaliza a fase de scan com prioridade e justificativa
  - O relatório final mostra antes, depois e economia projetada
  - O modo `--post` consegue reutilizar artefatos anteriores sem reexecutar todo o
    pipeline
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


# Task: Optimize - Post Economy

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-post-economy` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: optimize-post-economy
name: "Optimize Post Economy"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Consolida análise em relatório ROI, calcula economia pós-refatoração e emite o before/after final da otimização."
absorbs:
  - optimize-roi-report
```

## Purpose

Transformar a análise em plano executável com ROI calculado e, em seguida, fechar a otimização com métrica de economia, breakdown por script e comparação consolidada. Cobre tanto a priorização inicial (scan) quanto o relatório final (post).

## Inputs

```yaml
inputs:
  analysis_table:
    type: object
    required: true
  scope_patch_plan:
    type: object
    required: false
  gatekeeper_findings:
    type: object
    required: false
  empirical_results:
    type: object
    required: false
  bias_findings:
    type: object
    required: false
```

## Workflow / Steps

### Step 0: ROI Calculation (absorbed from optimize-roi-report)

#### Step 0.1: Estimar custo e ganho

- Projetar custo atual por task.
- Projetar economia após Worker/Hybrid/binary checkpoint conversion.

#### Step 0.2: Priorizar

- Ordenar por ROI, risco e facilidade de implementação.
- Separar recomendações para `scan`, `implement` e `hybrid`.

#### Step 0.3: Emitir relatório ROI

- Gerar relatório de análise e backlog de implementação.

### Step 1: Inventariar mudanças

- Capturar arquivos tocados, executor anterior e executor final.

### Step 2: Calcular economia

- Recalcular custo projetado.
- Gerar before/after e breakdown por script ou task.

### Step 3: Emitir relatório final

- Consolidar economia, risco residual e próximos passos.

## Output

```yaml
output:
  schema:
    roi_summary: []
    priority_matrix: []
    scan_report: "path or inline payload"
    changed_files: []
    token_economics: []
    comparison_table: []
    final_economy_report: "path or inline payload"
```

## Acceptance Criteria

- [ ] O relatório ROI finaliza a fase de scan com prioridade e justificativa
- [ ] O relatório final mostra antes, depois e economia projetada
- [ ] O modo `--post` consegue reutilizar artefatos anteriores sem reexecutar todo o pipeline

## Related Documents

- `optimize.md`
- `optimize-empirical-validation.md`
- `optimize-hybrid-executor.md`

_Task Version: 2.0.0_
_Absorbs: optimize-roi-report (v1.0.0)_
