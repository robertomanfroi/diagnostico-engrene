<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-validation
  task_name: Squad Fusion - Validation
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
  - Rodar quality gates
  - Emitir decisão
  acceptance_criteria:
  - A fusão não avança cegamente para a carga final [threshold: >= 1]
  - O relatório diferencia warning de blocker [threshold: >= 2]
  - O workflow sabe quando pedir checkpoint humano [threshold: >= 1]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Squad Fusion - Validation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-validation` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: squad-fusion-validation
name: "Squad Fusion Validation"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Roda quality gates antes da criação da estrutura final e decide se a fusão pode prosseguir sem degradar o sistema."
```

## Purpose

Validar integridade, consistência e qualidade do workspace intermediário antes da fase de carga final.

## Workflow / Steps

### Step 1: Rodar quality gates

- Validar integridade estrutural do workspace temporário.
- Verificar referências quebradas, conflitos pendentes e qualidade mínima.

### Step 2: Emitir decisão

- Produzir `validation_status`, `validation_report` e `issues_to_fix`.
- Em `quality`, exigir checkpoint humano quando necessário.

## Output

```yaml
output:
  schema:
    validation_status: "pass | warn | fail"
    validation_report: markdown
    issues_to_fix: []
```

## Acceptance Criteria

- [ ] A fusão não avança cegamente para a carga final [threshold: >= 1]
- [ ] O relatório diferencia warning de blocker [threshold: >= 2]
- [ ] O workflow sabe quando pedir checkpoint humano [threshold: >= 1]
