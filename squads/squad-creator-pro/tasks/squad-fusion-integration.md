<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-integration
  task_name: Squad Fusion - Integration
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
  - Testar operação do squad
  - Emitir relatório de integração
  acceptance_criteria:
  - O squad fusionado é testado antes do cleanup [threshold: >= 1]
  - Falhas críticas impedem avanço [threshold: >= 1]
  - O report de integração é legível e acionável [threshold: score >= 0.8]
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


# Task: Squad Fusion - Integration

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-integration` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: squad-fusion-integration
name: "Squad Fusion Integration"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Executa smoke tests e valida se o squad fusionado está operacional antes da sincronização de comandos e cleanup."
```

## Purpose

Confirmar que o squad recém-criado é realmente utilizável antes de qualquer etapa irreversível.

## Workflow / Steps

### Step 1: Testar operação do squad

- Rodar checks mínimos de estrutura, entrada, comandos e rotas internas.
- Identificar regressões causadas pela fusão.

### Step 2: Emitir relatório de integração

- Produzir `test_status` e `test_report`.
- Bloquear cleanup quando houver falha crítica.

## Output

```yaml
output:
  schema:
    test_status: "pass | warn | fail"
    test_report: markdown
```

## Acceptance Criteria

- [ ] O squad fusionado é testado antes do cleanup [threshold: >= 1]
- [ ] Falhas críticas impedem avanço [threshold: >= 1]
- [ ] O report de integração é legível e acionável [threshold: score >= 0.8]
