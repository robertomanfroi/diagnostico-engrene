<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-workflow-apply
  task_name: Optimize Workflow - Apply & Validate
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 35m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Confirmar pré-condições
  - Aplicar otimizações
  - Atualizar versão
  - Validar YAML
  - Validar estrutura
  acceptance_criteria:
  - Nenhuma mudança é aplicada sem backup
  - O diff estrutural fica rastreável por workflow
  - Workflow otimizado parseia
  - Falhas estruturais bloqueiam fechamento e sinalizam rollback
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


# Task: Optimize Workflow - Apply & Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-workflow-apply` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |
| **Merge Note** | Absorveu `optimize-workflow-validate` v1.0.0 |

## Metadata

```yaml
id: optimize-workflow-apply
name: "Optimize Workflow Apply & Validate"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica mudanças estruturais aprovadas no workflow, exigindo backup e rastreabilidade, depois valida sintaxe, alcançabilidade e integridade estrutural antes do handoff final."
```

## Purpose

Executar o modo `--implement`. Esta task aplica otimizações no YAML do workflow sem pular backup, diff plan ou rastreabilidade e fecha com validação determinística garantindo que o workflow otimizado ainda parseia, continua alcançável e não introduziu ciclo ou ruptura.

## Inputs

```yaml
inputs:
  implementation_backlog:
    type: object
    required: true
  workflow_files:
    type: array
    required: true
```

## Workflow / Steps

### Step 1: Confirmar pré-condições

- Backup existe.
- Scan foi concluído.

### Step 2: Aplicar otimizações

- Remover/merge de fases.
- Introduzir paralelização quando segura.
- Ajustar checkpoints e executor.

### Step 3: Atualizar versão

- Registrar versão e nota de otimização.

### Step 4: Validar YAML

- Confirmar parse do arquivo.

### Step 5: Validar estrutura

- Estados alcançáveis.
- Sequência coerente.
- Sem referência quebrada evidente.
- Se falha: sinalizar rollback, bloquear fechamento.

## Output

```yaml
output:
  schema:
    changed_workflows: []
    backup_paths: []
    version_updates: []
    validation_results: []
    rollback_required: false
```

## Acceptance Criteria

- [ ] Nenhuma mudança é aplicada sem backup
- [ ] O diff estrutural fica rastreável por workflow
- [ ] Workflow otimizado parseia
- [ ] Falhas estruturais bloqueiam fechamento e sinalizam rollback

## Related Documents

- `optimize-workflow.md`
- `optimize-workflow-report.md`

_Task Version: 2.0.0_
_Merge: optimize-workflow-validate v1.0.0 absorbed into this task_
