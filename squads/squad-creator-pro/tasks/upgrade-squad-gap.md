<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad-gap
  task_name: Upgrade Squad - Gap Analysis
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
  - Rodar a análise estrutural herdada
  - Adicionar gaps qualitativos do pack
  acceptance_criteria:
  - A análise estrutural do base continua sendo a verdade canônica
  - Os gaps qualitativos não contaminam o score estrutural
  - O output já distingue o que pode ser automatizado do que exige evidência ou pesquisa
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


# Task: Upgrade Squad - Gap Analysis

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-gap` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: upgrade-squad-gap
name: "Upgrade Squad Gap Analysis"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Reusa a análise estrutural do base e adiciona a leitura qualitativa e de governança avançada que o pack pro exige."
```

## Purpose

Executar a análise estrutural do base e produzir um relatório dual-track:
- `structural_gaps`: baseline canônico do `squad-creator`
- `qualitative_gaps`: lacunas de DNA, exemplos, roteamento, governança e assets avançados do overlay

## Workflow / Steps

### Step 1: Rodar a análise estrutural herdada

- Ler `squads/squad-creator/tasks/upgrade-squad-gap.md` por completo.
- Preservar score estrutural, prioridades e pesos do base.

### Step 2: Adicionar gaps qualitativos do pack

- Verificar `voice_dna`, `output_examples`, `anti_patterns`, `handoff_to` e assets de routing quando houver agents especializados.
- Verificar `workspace_integration`, `journey_log`, `artifact_contracts` e `model-routing` quando o target exigir governança avançada.
- Classificar cada item como `structural`, `qualitative-manual` ou `qualitative-research`.

## Output

```yaml
output:
  schema:
    structural_gaps: {}
    qualitative_gaps:
      manual: []
      research_required: []
    merged_priority_view:
      critical: []
      high: []
      medium: []
      low: []
```

## Acceptance Criteria

- [ ] A análise estrutural do base continua sendo a verdade canônica
- [ ] Os gaps qualitativos não contaminam o score estrutural
- [ ] O output já distingue o que pode ser automatizado do que exige evidência ou pesquisa

## Related Documents

- `squads/squad-creator/tasks/upgrade-squad-gap.md`
- `upgrade-squad-plan.md`
