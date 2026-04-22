---
task-id: collect-sources-quality-gate
name: "Quality Gate - GO/NO-GO Decision and Output Generation"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Quality gate decision requires judgment on readiness for extraction. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 5 min
complexity: medium

inputs:
  required:
    - sources_by_tier: "Fontes classificadas por tier"
    - coverage_report: "Resultado da validacao de cobertura"
    - gap_analysis: "Lacunas identificadas com plano de aquisicao"
    - mind_name: "Nome do expert"
    - domain: "Area de expertise"

outputs:
  primary:
    - sources_inventory: "Inventario final validado com decisao GO/CONDITIONAL/NO-GO"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources-quality-gate
  task_name: Quality Gate - GO/NO-GO Decision and Output Generation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 5m
  domain: Operational
  input:
  - '{''sources_by_tier'': ''Fontes classificadas por tier''}'
  - '{''coverage_report'': ''Resultado da validacao de cobertura''}'
  - '{''gap_analysis'': ''Lacunas identificadas com plano de aquisicao''}'
  - '{''mind_name'': ''Nome do expert''}'
  - '{''domain'': ''Area de expertise''}'
  output:
  - '{''sources_inventory'': ''Inventario final validado com decisao GO/CONDITIONAL/NO-GO''}'
  action_items:
  - Execute GO/NO-GO Checklist
  - Render Decision
  - Generate Sources Inventory (Final Output)
  - Quality Check Summary
  acceptance_criteria:
  - 10+ fontes totais identificadas [threshold: >= 10]
  - 5+ fontes Tier 1 (primarias) [threshold: >= 5]
  - 3+ tipos diferentes de fonte [threshold: >= 3]
  - 5+ horas OU 200+ paginas de conteudo [threshold: >= 5h OR >= 200p]
  - Framework principal triangulado (3+ fontes) [threshold: >= 3]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Quality Gate - GO/NO-GO Decision and Output Generation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `collect-sources-quality-gate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `collect-sources` (orchestrator stub)
- **Sequence:** Phase 5 of 5 (final)
- **Previous Task:** `collect-sources-gap-analysis`

## Purpose

Execute the final quality gate for source collection. Evaluate the GO/NO-GO checklist based on all upstream outputs, render the decision, and generate the consolidated `sources_inventory` output artifact. This is the decision point that determines whether extraction can proceed.

> **Rule:** NUNCA prosseguir para extracao sem validar fontes suficientes.

## Prerequisites

- All 4 previous phases completed (discover, classify, validate, gap-analysis)
- All upstream outputs available

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `sources_by_tier` | Yes | Classified sources with tier assignments |
| `coverage_report` | Yes | Coverage validation with check statuses |
| `gap_analysis` | Yes | Gap identification with acquisition plan |
| `mind_name` | Yes | Expert name |
| `domain` | Yes | Domain of expertise |

## Workflow / Steps

### Step 1: Execute GO/NO-GO Checklist

Evaluate each check using upstream data:

```yaml
go_no_go_checklist:
  # Quantidade (BLOCKING)
  - check: "10+ fontes totais"
    status: "PASS|FAIL"
    blocking: true

  - check: "5+ fontes Tier 1 (primarias)"
    status: "PASS|FAIL"
    blocking: true

  # Diversidade (BLOCKING)
  - check: "3+ tipos diferentes de fonte"
    status: "PASS|FAIL"
    blocking: true

  # Volume (BLOCKING)
  - check: "5+ horas de audio/video OU 200+ paginas"
    status: "PASS|FAIL"
    blocking: true

  # Triangulacao (BLOCKING)
  - check: "Framework principal confirmado em 3+ fontes"
    status: "PASS|FAIL"
    blocking: true

  # Temporal (WARNING)
  - check: "Cobertura de 2+ periodos temporais"
    status: "PASS|WARNING"
    blocking: false
```

### Step 2: Render Decision

```yaml
decision:
  blocking_checks_passed: 0/5

  status: "GO|CONDITIONAL|NO-GO"

  # GO: Todos blocking checks PASS
  # CONDITIONAL: 4/5 blocking, com plano para preencher
  # NO-GO: <4/5 blocking - precisa mais pesquisa

  conditions_if_conditional:
    - ""

  next_action: ""
```

**Decision Rules:**
- **GO (5/5 blocking PASS):** All blocking checks satisfied. Ready for extraction.
- **CONDITIONAL (4/5 blocking PASS):** One blocking check failed but gap_analysis has a viable acquisition plan. List conditions.
- **NO-GO (<4/5 blocking PASS):** Insufficient sources. Return to discovery phase or request user materials.

### Step 3: Generate Sources Inventory (Final Output)

Assemble the consolidated `sources_inventory` artifact with these sections:

- **metadata:** mind_name, domain, collection_date, total_sources, tier_1_count, quality_status
- **tier_1_primary:** Each source with id (S01...), title, type, year, url, estimated_volume, key_topics, triangulates
- **tier_2_secondary:** Each source with id (S06...), title, type, url
- **tier_3_tertiary:** Each source with id (S10...), title, type, url
- **validation:** total_sources, tier_1_count, type_diversity, content_volume (hours/pages), temporal_periods, triangulation_score
- **gaps:** Each gap with description, risk (alto/medio/baixo), mitigation
- **decision:** status (GO/CONDITIONAL/NO-GO), blocking_passed (X/5), ready_for_extraction, conditions

### Step 4: Quality Check Summary

Present final checklist:

- [ ] 10+ fontes totais identificadas
- [ ] 5+ fontes Tier 1 (primarias)
- [ ] 3+ tipos diferentes de fonte
- [ ] 5+ horas OU 200+ paginas de conteudo
- [ ] Framework principal triangulado (3+ fontes)
- [ ] Decisao GO ou CONDITIONAL com plano

**BLOCKING:** Se <4 checks passam, resultado e NO-GO, precisa mais pesquisa.

## Output

The `sources_inventory` YAML artifact as described in Step 3. This is the primary deliverable of the entire `collect-sources` pipeline.

## Acceptance Criteria

- [ ] All 5 blocking checks evaluated with actual data from upstream phases [threshold: >= 5]
- [ ] Decision rendered as GO, CONDITIONAL, or NO-GO with correct logic [threshold: >= 1 decision]
- [ ] CONDITIONAL decisions include specific conditions and acquisition plan [threshold: >= 1 plan if CONDITIONAL]
- [ ] Sources inventory generated with all sections (metadata, tiers, validation, gaps, decision) [threshold: >= 5 sections]
- [ ] Each source has unique ID (S01, S02...) for downstream reference [threshold: 100% sources with ID]
- [ ] Quality check summary presented to user [threshold: >= 1 summary]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CSR-003 | Quality gate decision must not be bypassed | Verify `go_no_go_checklist` is completed before handoff | VETO - BLOCK. Complete quality gate evaluation before allowing extraction to proceed. |
| VETO-CSR-004 | `min_sources` and `domain_validation` must pass | Verify minimum requirements met | VETO - BLOCK. Stop handoff until satisfied. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `collect-sources.md` | Parent orchestrator |
| `collect-sources-gap-analysis.md` | Previous phase (gap analysis) |
| `auto-acquire-sources.md` | Referenced for re-acquisition if NO-GO |
| `extract-knowledge.md` | Downstream consumer (extraction phase) |
