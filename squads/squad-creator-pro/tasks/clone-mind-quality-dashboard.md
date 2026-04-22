<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: clone-mind-quality-dashboard
  task_name: Clone Mind Quality Dashboard
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Aggregate Clone Metrics
  - Render Dashboard
  - Produce Recommendations
  acceptance_criteria:
  - O dashboard é específico de clone, não analytics genérico de squad [threshold: >= 1 clone-specific dashboard]
  - As métricas do workflow são refletidas explicitamente no output [threshold: >= 6 metrics]
  - O artefato final lista gaps e recommendations acionáveis [threshold: >= 1 recommendation]
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
  Domain: Tactical
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Clone Mind Quality Dashboard

**Task ID:** clone-mind-quality-dashboard
**Version:** 1.0.0
**Purpose:** Gerar dashboard de qualidade específico de clone a partir de fontes, DNA extraído e resultado do smoke test
**Orchestrator:** @oalanicolas
**Mode:** Reporting

---

## Purpose

Esta task existe para a fase `quality-dashboard-generation` de `wf-clone-mind.yaml`.

Ela NÃO usa analytics genérico de squad. O objetivo é consolidar métricas específicas do clone:

- quantidade e qualidade de fontes;
- cobertura de Voice DNA;
- cobertura de Thinking DNA;
- resultado do smoke test;
- `fidelity_estimate`.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `sources_inventory` | file/object | Yes | Inventário de fontes |
| `voice_dna` | file/object | Yes | Artefato final de Voice DNA |
| `thinking_dna` | file/object | Yes | Artefato final de Thinking DNA |
| `smoke_test_result` | file/object | Yes | Resultado do smoke test comportamental |
| `fidelity_estimate` | number/string | No | Estimativa consolidada de fidelidade |

---

## Workflow

### Step 1: Aggregate Clone Metrics

Calcular e consolidar:

- `sources_count`
- `tier_1_ratio`
- `voice_score`
- `thinking_score`
- `smoke_test_result`
- `fidelity_estimate`

### Step 2: Render Dashboard

Gerar dashboard usando:

- `squads/squad-creator/templates/quality-dashboard-tmpl.md`

### Step 3: Produce Recommendations

Listar gaps prioritários e próximas ações para elevar fidelidade e robustez do clone.

---

## Output

```yaml
output:
  primary:
    - quality_dashboard
  artifacts:
    - quality_dashboard.md
```

---

## Acceptance Criteria

- [ ] O dashboard é específico de clone, não analytics genérico de squad [threshold: >= 1 clone-specific dashboard]
- [ ] As métricas do workflow são refletidas explicitamente no output [threshold: >= 6 metrics]
- [ ] O artefato final lista gaps e recommendations acionáveis [threshold: >= 1 recommendation]

---

## Related Documents

- `workflows/wf-clone-mind.yaml` -- fase consumidora
- `squads/squad-creator/templates/quality-dashboard-tmpl.md` -- template canônico

---

_Task Version: 1.0.0_
_Role: clone-specific quality dashboard contract_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed clone-mind-quality-dashboard output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified
