---
task-id: collect-sources-gap-analysis
name: "Analyze Source Gaps and Plan Acquisition"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Gap analysis requires judgment on importance and acquisition strategy. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 5 min
complexity: low

inputs:
  required:
    - coverage_report: "Resultado da validacao de cobertura (output de collect-sources-validate)"
    - sources_by_tier: "Fontes classificadas por tier"

outputs:
  primary:
    - gap_analysis: "Lacunas identificadas com plano de aquisicao priorizado"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources-gap-analysis
  task_name: Analyze Source Gaps and Plan Acquisition
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 5m
  domain: Tactical
  input:
  - '{''coverage_report'': ''Resultado da validacao de cobertura (output de collect-sources-validate)''}'
  - '{''sources_by_tier'': ''Fontes classificadas por tier''}'
  output:
  - '{''gap_analysis'': ''Lacunas identificadas com plano de aquisicao priorizado''}'
  action_items:
  - Identify Gaps from Failed Checks
  - Prioritize Gaps
  - Create Acquisition Plan
  acceptance_criteria:
  - All FAIL and WARNING checks from coverage_report mapped to specific gaps [threshold: 100% mapped]
  - Each gap classified by importance (critico/importante/desejavel) [threshold: 100% classified]
  - Acquisition plan created with specific actions for critical and important gaps [threshold: >= 1 plan per critical gap]
  - Critical gap count computed for quality gate input [threshold: >= 1 count]
  - Estimated time provided for critical acquisitions [threshold: >= 1 estimate per critical gap]
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


# Task: Analyze Source Gaps and Plan Acquisition

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `collect-sources-gap-analysis` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `collect-sources` (orchestrator stub)
- **Sequence:** Phase 4 of 5
- **Previous Task:** `collect-sources-validate`
- **Next Task:** `collect-sources-quality-gate`

## Purpose

Identify specific gaps in the source collection based on the coverage report. For each gap, assess importance and create a prioritized acquisition plan. This ensures the quality gate decision in the next phase has actionable remediation paths.

## Prerequisites

- `collect-sources-validate` task completed
- `coverage_report` output available with check statuses

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `coverage_report` | Yes | Coverage validation results with PASS/FAIL checks |
| `sources_by_tier` | Yes | Classified sources for cross-reference |

## Workflow / Steps

### Step 1: Identify Gaps from Failed Checks

Review each FAIL or WARNING check from coverage_report and translate into specific gaps:

```yaml
gaps_identified:
  missing_types:
    - type: ""
      importance: "critico|importante|desejavel"
      action: ""

  temporal_gaps:
    - period: ""
      why_matters: ""
      action: ""

  depth_gaps:
    - area: ""
      current_coverage: ""
      needed: ""
```

**Gap Categories:**
- **missing_types:** Source types not represented (e.g., no video content, no books)
- **temporal_gaps:** Time periods with no coverage (e.g., expert's early career)
- **depth_gaps:** Topics with insufficient depth (e.g., methodology documented only superficially)

### Step 2: Prioritize Gaps

Classify each gap by importance:

| Importance | Criteria | Action Required |
|------------|----------|-----------------|
| **Critico** | Blocks GO decision, affects core framework triangulation | Must resolve before quality gate |
| **Importante** | Reduces clone fidelity but does not block | Should resolve, can proceed CONDITIONAL |
| **Desejavel** | Nice to have, marginal improvement | Document for future enhancement |

### Step 3: Create Acquisition Plan

For each gap, define how to fill it:

```yaml
acquisition_plan:
  priority_1_critical:
    - source: ""
      how_to_get: ""
      estimated_time: ""

  priority_2_important:
    - source: ""
      how_to_get: ""

  priority_3_nice_to_have:
    - source: ""
```

**Acquisition methods:**
- Web search (specific queries)
- User-provided materials request
- Auto-acquire task re-run with refined queries
- Manual research (podcasts, interviews, archives)

## Output

```yaml
gap_analysis:
  gaps_identified:
    missing_types: []
    temporal_gaps: []
    depth_gaps: []
  total_gaps: 0
  critical_gaps: 0
  acquisition_plan:
    priority_1_critical: []
    priority_2_important: []
    priority_3_nice_to_have: []
```

## Acceptance Criteria

- [ ] All FAIL and WARNING checks from coverage_report mapped to specific gaps [threshold: 100% mapped]
- [ ] Each gap classified by importance (critico/importante/desejavel) [threshold: 100% classified]
- [ ] Acquisition plan created with specific actions for critical and important gaps [threshold: >= 1 plan per critical gap]
- [ ] Critical gap count computed for quality gate input [threshold: >= 1 count]
- [ ] Estimated time provided for critical acquisitions [threshold: >= 1 estimate per critical gap]

## Veto Conditions

None specific to this phase. Downstream quality gate (VETO-CSR-003) uses this output.

## Related Documents

| Document | Relationship |
|----------|-------------|
| `collect-sources.md` | Parent orchestrator |
| `collect-sources-validate.md` | Previous phase (coverage validation) |
| `collect-sources-quality-gate.md` | Next phase (GO/NO-GO decision) |
