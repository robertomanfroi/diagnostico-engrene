---
task-id: extract-expert-gold-filter
name: "Gold Filter — Diff, Classify, and Rank Insights"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Diffing against existing knowledge and impact classification require semantic judgment."
haiku_eligible: false
estimated-time: 15 min
complexity: high

inputs:
  required:
    - merged_extraction: "Unified extraction from Phase 1"
    - existing_knowledge: "Baseline from Phase 0"
  optional:
    - source_context: "Description of source for attribution"

outputs:
  primary:
    - gold_summary: "Ranked list of new insights with impact classification"
    - classified_insights: "All insights classified as NEW/KNOWN/CONTRADICTS/ENRICHES"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold-filter
  task_name: Gold Filter — Diff, Classify, and Rank Insights
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Operational
  input:
  - '{''merged_extraction'': ''Unified extraction from Phase 1''}'
  - '{''existing_knowledge'': ''Baseline from Phase 0''}'
  - '{''source_context'': ''Description of source for attribution''}'
  output:
  - '{''gold_summary'': ''Ranked list of new insights with impact classification''}'
  - '{''classified_insights'': ''All insights classified as NEW/KNOWN/CONTRADICTS/ENRICHES''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Ranked list of new insights with impact classification'
  - Task output validated against quality standards
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Gold Filter -- Diff, Classify, and Rank Insights

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-expert-gold-filter` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `extract-expert-gold` (orchestrator stub)
- **Sequence:** Phase 3 of 5
- **Previous Task:** `extract-expert-gold-multi-lense`
- **Next Task:** `extract-expert-gold-enrichment`

## Purpose

Separate genuinely NEW knowledge from what we already have. Classify every extracted insight against the existing baseline, assign impact levels, and produce a ranked gold summary for human review before enrichment proceeds.

## Prerequisites

- `merged_extraction` must contain at least 1 insight
- `existing_knowledge` baseline must be available from Phase 0

## Step 2.1: Diff Against Baseline

```yaml
for each insight in merged_extraction:
  compare_against: existing_knowledge.files

  classify:
    NEW:
      criteria: "Insight not present in any existing reference file"
      action: "Include in enrichment"
    KNOWN:
      criteria: "Insight already documented (same or equivalent)"
      action: "Skip (optionally note as corroboration)"
    CONTRADICTS:
      criteria: "Insight conflicts with existing documented data"
      action: "Flag for human review, include both versions"
    ENRICHES:
      criteria: "Adds depth/detail to existing insight"
      action: "Include as enrichment to existing section"
```

## Step 2.2: Impact Classification

```yaml
for each NEW or ENRICHES insight:
  classify_impact:
    GAME_CHANGER:
      criteria: |
        - Changes fundamental approach or mental model
        - Backed by data/case study with measurable results
        - Applicable immediately to current workflows
      examples:
        - "Custo de checkout > ROAS como metrica soberana"
        - "Formato muda conversao 2X com mesma copy"

    TACTICAL:
      criteria: |
        - Specific technique or process improvement
        - Clear execution steps
        - Incremental improvement, not paradigm shift
      examples:
        - "Cost cap deve ser proximo ao ticket medio do funil"
        - "Trial 7 dias no upsell com one-click"

    CONTEXTUAL:
      criteria: |
        - Background information, philosophy, or market context
        - Useful for understanding but not directly actionable
        - Supports other insights
      examples:
        - "Digital como falha na Matrix"
        - "Historia do expert no perpetuo"
```

## Step 2.3: Gold Summary

```yaml
output:
  gold_summary:
    total_new: N
    total_known: N
    total_contradicts: N
    total_enriches: N
    by_impact:
      game_changer: N
      tactical: N
      contextual: N
    top_insights:  # max 15, ranked by impact
      - insight: "{description}"
        impact: "GAME_CHANGER"
        confidence: "[DOC]"
        timestamp: "HH:MM:SS"
        analyst: "{who found it}"
```

## Elicitation Point

**Checkpoint:** Present gold summary to user. Confirm before enriching reference files.

> "Here is the gold summary with N new insights (X game-changers, Y tactical, Z contextual). Proceed with enrichment?"

**Default:** Yes.

## Output

Pass `gold_summary` and `classified_insights` to the next task (`extract-expert-gold-enrichment`).

---

_Task Version: 1.0.0_
_Parent: extract-expert-gold_
_Phase: 2 -- Gold Filter_

## Acceptance Criteria

- [ ] Output artifact produced: Ranked list of new insights with impact classification
- [ ] Task output validated against quality standards
