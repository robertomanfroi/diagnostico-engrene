---
task-id: auto-acquire-sources-consolidate
name: "Consolidate, Prioritize & Output"
version: 1.0.0
execution_type: Hybrid
model: Haiku
model_rationale: "Aggregation and formatting are deterministic. LLM only summarizes."
haiku_eligible: true
estimated-time: 5 min
complexity: low

inputs:
  required:
    - youtube_sources: "From Phase 1"
    - book_sources: "From Phase 1"
    - podcast_sources: "From Phase 2"
    - article_sources: "From Phase 2"

outputs:
  primary:
    - acquired_sources: "Complete inventory of all acquired sources"
    - sources_inventory.yaml: "Structured inventory file"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: auto-acquire-sources-consolidate
  task_name: Consolidate, Prioritize & Output
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 5m
  domain: Operational
  input:
  - '{''youtube_sources'': ''From Phase 1''}'
  - '{''book_sources'': ''From Phase 1''}'
  - '{''podcast_sources'': ''From Phase 2''}'
  - '{''article_sources'': ''From Phase 2''}'
  output:
  - '{''acquired_sources'': ''Complete inventory of all acquired sources''}'
  - '{''sources_inventory.yaml'': ''Structured inventory file''}'
  action_items:
  - Merge with Existing Sources
  - Prioritize for Download
  - Generate Final Output
  acceptance_criteria:
  - All sources from Phase 1 and Phase 2 consolidated
  - Tier classification applied to all sources
  - Download queue prioritized (immediate, if-time, backup)
  - Acquisition summary with counts and estimated content
  - sources_inventory.yaml written
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


# Task: Consolidate, Prioritize & Output

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-acquire-sources-consolidate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `auto-acquire-sources` (orchestrator stub)
- **Sequence:** Phase 3 of 3
- **Previous Task:** `auto-acquire-sources-expand`
- **Next Task:** None (final phase)

## Purpose

Merge all discovered sources, generate acquisition summary, create prioritized download queue, and produce final structured output.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AAS-002 | Must not overwrite existing curated sources without confirmation | BLOCK - Prompt for merge/replace strategy |

## Workflow / Steps

### Step 1: Merge with Existing Sources

```yaml
acquisition_summary:
  youtube_found: 0
  books_found: 0
  podcasts_found: 0
  articles_found: 0
  total_new: 0
  by_tier:
    tier_1: 0
    tier_2: 0
    tier_3: 0
  estimated_content:
    hours: 0
    pages: 0
```

### Step 2: Prioritize for Download

```yaml
download_queue:
  priority_1_immediate:
    - source_id: ""
      type: ""
      action: "download_transcript|download_pdf|save_url"
  priority_2_if_time:
    - source_id: ""
      type: ""
      action: ""
  priority_3_backup:
    - source_id: ""
      type: ""
      action: ""
```

### Step 3: Generate Final Output

```yaml
acquired_sources:
  metadata:
    mind_name: ""
    domain: ""
    acquisition_date: ""
    total_found: 0
    auto_acquired: true
  youtube:
    count: 0
    items: [...]
  books:
    count: 0
    items: [...]
  podcasts:
    count: 0
    items: [...]
  articles:
    count: 0
    items: [...]
```

## Output

```yaml
acquired_sources: { complete inventory }
download_queue: { prioritized actions }
```

## Acceptance Criteria

- [ ] All sources from Phase 1 and Phase 2 consolidated
- [ ] Tier classification applied to all sources
- [ ] Download queue prioritized (immediate, if-time, backup)
- [ ] Acquisition summary with counts and estimated content
- [ ] sources_inventory.yaml written

## Related Documents

| Document | Relationship |
|----------|-------------|
| `auto-acquire-sources.md` | Parent orchestrator |
| `auto-acquire-sources-expand.md` | Previous phase |
| `collect-sources.md` | Integration point |
