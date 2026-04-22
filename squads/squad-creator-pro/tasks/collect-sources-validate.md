---
task-id: collect-sources-validate
name: "Validate Source Coverage and Triangulation"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Coverage validation and triangulation require semantic judgment to assess sufficiency. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - sources_by_tier: "Fontes classificadas por tier (output de collect-sources-classify)"
    - mind_name: "Nome do expert"
    - domain: "Area de expertise"

outputs:
  primary:
    - coverage_report: "Resultado da validacao de cobertura com checklist e triangulacao"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources-validate
  task_name: Validate Source Coverage and Triangulation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''sources_by_tier'': ''Fontes classificadas por tier (output de collect-sources-classify)''}'
  - '{''mind_name'': ''Nome do expert''}'
  - '{''domain'': ''Area de expertise''}'
  output:
  - '{''coverage_report'': ''Resultado da validacao de cobertura com checklist e triangulacao''}'
  action_items:
  - Minimum Requirements Checklist
  - Triangulation Validation
  - Compute Coverage Score
  acceptance_criteria:
  - All 6 minimum requirement checks evaluated with actual counts [threshold: >= 6]
  - All 3 triangulation claims assessed against source evidence [threshold: >= 3]
  - Each check marked PASS, WARNING, or FAIL with actual values [threshold: >= 6 checks marked]
  - Coverage score computed with totals [threshold: >= 1 score]
  - Content volume estimated from Tier 0+1 sources (hours and pages) [threshold: >= 5h OR >= 200p]
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


# Task: Validate Source Coverage and Triangulation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `collect-sources-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `collect-sources` (orchestrator stub)
- **Sequence:** Phase 3 of 5
- **Previous Task:** `collect-sources-classify`
- **Next Task:** `collect-sources-gap-analysis`

## Purpose

Validate that the classified source collection meets minimum requirements for a high-fidelity mind clone. Check quantity, diversity, volume, and triangulation of key claims. This phase determines whether the source base is sufficient for extraction or whether gaps need to be filled.

> **Core Principle:** "Single source = hypothesis; three sources = pattern"

## Prerequisites

- `collect-sources-classify` task completed
- `sources_by_tier` output available with tier distribution

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `sources_by_tier` | Yes | Classified source list with tier assignments |
| `mind_name` | Yes | Expert name for context |
| `domain` | Yes | Domain for relevance assessment |

## Workflow / Steps

### Step 1: Minimum Requirements Checklist

Evaluate each requirement against the classified sources:

```yaml
minimum_requirements:
  # Quantidade
  total_sources:
    required: 10
    actual: 0
    status: "PASS|FAIL"

  tier_1_sources:
    required: 5
    actual: 0
    status: "PASS|FAIL"

  # Diversidade de Tipos
  source_types:
    required: 3  # diferentes tipos
    actual: 0
    types_found: []
    status: "PASS|FAIL"

  # Volume de Conteudo
  content_volume:
    audio_video_hours:
      required: 5
      actual: 0
      status: "PASS|FAIL"

    text_pages:
      required: 200
      actual: 0
      status: "PASS|FAIL"

  # Cobertura Temporal
  temporal_coverage:
    periods_covered: []  # ex: "2010-2015", "2020-present"
    has_multiple_periods:
      required: true
      actual: false
      status: "PASS|FAIL"
```

### Step 2: Triangulation Validation

For important claims about the expert, verify 3+ independent sources confirm each:

```yaml
triangulation_check:
  main_framework:
    claim: "O framework principal do expert"
    sources_confirming: []
    count: 0
    status: "PASS (3+) | WARNING (2) | FAIL (1)"

  core_principles:
    claim: "Principios fundamentais"
    sources_confirming: []
    count: 0
    status: ""

  signature_methodology:
    claim: "Metodologia distintiva"
    sources_confirming: []
    count: 0
    status: ""
```

### Step 3: Compute Coverage Score

Summarize all checks:

```yaml
coverage_score:
  checks_total: 6
  checks_passed: 0
  checks_warning: 0
  checks_failed: 0
  triangulation_claims: 3
  triangulation_validated: 0
```

## Output

```yaml
coverage_report:
  minimum_requirements:
    total_sources: { required: 10, actual: 0, status: "" }
    tier_1_sources: { required: 5, actual: 0, status: "" }
    source_types: { required: 3, actual: 0, status: "" }
    audio_video_hours: { required: 5, actual: 0, status: "" }
    text_pages: { required: 200, actual: 0, status: "" }
    temporal_coverage: { required: true, actual: false, status: "" }
  triangulation_check:
    main_framework: { count: 0, status: "" }
    core_principles: { count: 0, status: "" }
    signature_methodology: { count: 0, status: "" }
  coverage_score:
    checks_passed: 0
    checks_total: 6
```

## Acceptance Criteria

- [ ] All 6 minimum requirement checks evaluated with actual counts [threshold: >= 6]
- [ ] All 3 triangulation claims assessed against source evidence [threshold: >= 3]
- [ ] Each check marked PASS, WARNING, or FAIL with actual values [threshold: >= 6 checks marked]
- [ ] Coverage score computed with totals [threshold: >= 1 score]
- [ ] Content volume estimated from Tier 0+1 sources (hours and pages) [threshold: >= 5h OR >= 200p]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CSR-004 | `min_sources` and `domain_validation` must pass | Verify `minimum_requirements.total_sources.actual` meets threshold | VETO - BLOCK handoff if not satisfied. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `collect-sources.md` | Parent orchestrator |
| `collect-sources-classify.md` | Previous phase (tier classification) |
| `collect-sources-gap-analysis.md` | Next phase (gap identification) |
