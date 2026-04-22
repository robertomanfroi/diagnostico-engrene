---
task-id: extract-expert-gold-validation
name: "Validation — Data Integrity and Extraction Report"
version: 1.0.0
execution_type: Automated
model: Sonnet
model_rationale: "Validation checks and report generation require contextual analysis of enriched files."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - enriched_files: "List of reference files modified (from Phase 3)"
    - gold_summary: "Ranked insights from Phase 2"
    - existing_knowledge: "Baseline from Phase 0"
    - expert_slug: "Expert identifier"
    - expert_name: "Human-readable expert name"
  optional:
    - source_context: "Description of source for attribution"
    - batch_id: "ETL batch identifier"

outputs:
  primary:
    - extraction_report: "Full summary with stats, conflicts, gaps, next steps"
    - validation_result: "PASS or FAIL with check details"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold-validation
  task_name: Validation — Data Integrity and Extraction Report
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 10m
  domain: Operational
  input:
  - '{''enriched_files'': ''List of reference files modified (from Phase 3)''}'
  - '{''gold_summary'': ''Ranked insights from Phase 2''}'
  - '{''existing_knowledge'': ''Baseline from Phase 0''}'
  - '{''expert_slug'': ''Expert identifier''}'
  - '{''expert_name'': ''Human-readable expert name''}'
  output:
  - '{''extraction_report'': ''Full summary with stats, conflicts, gaps, next steps''}'
  - '{''validation_result'': ''PASS or FAIL with check details''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Full summary with stats, conflicts, gaps, next steps'
  - Task output validated against quality standards
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
  Domain: Operational
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Validation -- Data Integrity and Extraction Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-expert-gold-validation` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Automated` |

## Metadata

- **Parent Task:** `extract-expert-gold` (orchestrator stub)
- **Sequence:** Phase 5 of 5
- **Previous Task:** `extract-expert-gold-enrichment`
- **Next Task:** None (terminal)

## Purpose

Ensure enrichment was clean and complete. Verify no data was lost, all new insights were written with proper markers, squad agnosticism is maintained, and generate a comprehensive extraction report.

## Prerequisites

- `enriched_files` must be a non-empty list from Phase 3
- Original reference files must still be accessible for diff comparison

## Step 4.1: Data Integrity Checks

```yaml
checks:
  - id: "EEG-VAL-001"
    check: "No existing data was deleted or overwritten"
    method: "Diff original vs new file, verify all original lines present"

  - id: "EEG-VAL-002"
    check: "All NEW insights were written"
    method: "Count insights routed vs insights in files"

  - id: "EEG-VAL-003"
    check: "Confidence markers present on all new entries"
    method: "Grep for lines without [DOC]/[REP]/[INF] in new sections"

  - id: "EEG-VAL-004"
    check: "Squad agnosticism maintained"
    method: "Scan for business-specific terms"

  - id: "EEG-VAL-005"
    check: "Source attribution on all new entries"
    method: "Grep for 'Source:' in new sections"
```

All 5 checks must pass for a PASS result.

## Step 4.2: Generate Extraction Report

```yaml
report:
  path: ".aiox/squad-runtime/etl/{batch_id}/extraction-report.md"
  sections:
    - summary: "Expert, source, duration, date"
    - baseline: "What we knew before"
    - extraction: "What each analyst found"
    - gold: "New insights ranked by impact"
    - enrichment: "Files modified with line counts"
    - conflicts: "Any contradictions found"
    - gaps: "What we still don't know"
    - next_steps: "Suggested follow-up (more sources, SOPs to create, etc.)"
```

## Output

Final outputs of the entire pipeline:

| Output | Location | Description |
|--------|----------|-------------|
| Enriched reference files | `squads/{squad}/data/references/` | Updated with new insights |
| Per-analyst extractions | `.aiox/squad-runtime/etl/{batch_id}/` | Raw extraction per analyst |
| Extraction report | `.aiox/squad-runtime/etl/{batch_id}/extraction-report.md` | Full summary with stats |
| Gold summary | `.aiox/squad-runtime/etl/{batch_id}/gold-summary.yaml` | Top insights ranked |

---

_Task Version: 1.0.0_
_Parent: extract-expert-gold_
_Phase: 4 -- Validation_

## Acceptance Criteria

- [ ] Output artifact produced: Full summary with stats, conflicts, gaps, next steps
- [ ] Task output validated against quality standards
