---
task-id: extract-expert-gold-multi-lense
name: "Multi-Lense Extraction — Parallel Analyst Dispatch"
version: 1.0.0
execution_type: Automated
model: Sonnet
model_rationale: "Multi-lense analysis requires deep contextual reasoning per analyst framework."
haiku_eligible: false
estimated-time: 20 min
complexity: high

inputs:
  required:
    - source_file: "Path to transcription file"
    - selected_analysts: "Confirmed list of analyst agents (from Phase 0)"
    - existing_knowledge: "Baseline from Phase 0"
  optional:
    - source_context: "Description of source for attribution"

outputs:
  primary:
    - merged_extraction: "Unified extraction with insights from all analysts"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold-multi-lense
  task_name: Multi-Lense Extraction — Parallel Analyst Dispatch
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 20m
  domain: Operational
  input:
  - '{''source_file'': ''Path to transcription file''}'
  - '{''selected_analysts'': ''Confirmed list of analyst agents (from Phase 0)''}'
  - '{''existing_knowledge'': ''Baseline from Phase 0''}'
  - '{''source_context'': ''Description of source for attribution''}'
  output:
  - '{''merged_extraction'': ''Unified extraction with insights from all analysts''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Unified extraction with insights from all analysts'
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


# Task: Multi-Lense Extraction -- Parallel Analyst Dispatch

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-expert-gold-multi-lense` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Automated` |

## Metadata

- **Parent Task:** `extract-expert-gold` (orchestrator stub)
- **Sequence:** Phase 2 of 5
- **Previous Task:** `extract-expert-gold-context-load`
- **Next Task:** `extract-expert-gold-filter`

## Purpose

Each analyst reads the FULL transcription through their specific framework lens. Analysts run in parallel, each extracting only what is relevant to their expertise. Results are collected and merged into a unified extraction.

## Prerequisites

- `selected_analysts` must be a non-empty list (confirmed in Phase 0)
- `source_file` must exist and be readable
- `existing_knowledge` baseline must be available

## Step 1.1: Parallel Agent Dispatch

```yaml
for each analyst in selected_analysts:
  dispatch:
    agent: "{analyst}"
    input: "{source_file}"
    instruction: |
      Read the full transcription. Extract ONLY what is relevant to your
      specific framework and expertise. For each insight extracted:

      1. Quote the exact words when possible (with timestamp if available)
      2. Assign confidence marker:
         - [DOC] = Direct explicit statement from expert
         - [REP] = Repeated/corroborated across multiple points
         - [INF] = Inferred from context or partial evidence
      3. Categorize: framework | tactic | metric | case_study | philosophy
      4. Note the timestamp or section reference

    output_format: yaml
    output_path: ".aiox/squad-runtime/etl/{batch_id}/{analyst}-extraction.yaml"
```

## Step 1.2: Collect and Merge Results

Wait for all agents to complete. Merge into unified extraction.

```yaml
merged_extraction:
  total_insights: N  # sum across all analysts
  by_analyst:
    - agent: "{name}"
      insights_found: N
      categories: {framework: N, tactic: N, metric: N, case_study: N, philosophy: N}
  by_confidence:
    DOC: N
    REP: N
    INF: N
```

## Validation

- All dispatched analysts must return results before proceeding
- If any analyst returns zero insights, log a warning but do not block
- Minimum 1 insight total required to proceed to Phase 2

## Output

Pass `merged_extraction` to the next task (`extract-expert-gold-filter`).

---

_Task Version: 1.0.0_
_Parent: extract-expert-gold_
_Phase: 1 -- Multi-Lense Extraction_

## Acceptance Criteria

- [ ] Output artifact produced: Unified extraction with insights from all analysts
- [ ] Task output validated against quality standards
