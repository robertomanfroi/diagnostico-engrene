---
task-id: extract-expert-gold-enrichment
name: "Enrichment — Merge Insights into Reference Files"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Routing insights to correct files and merge strategy require domain comprehension."
haiku_eligible: false
estimated-time: 15 min
complexity: high

inputs:
  required:
    - gold_summary: "Ranked insights from Phase 2"
    - classified_insights: "All insights classified as NEW/KNOWN/CONTRADICTS/ENRICHES"
    - expert_slug: "Expert identifier"
    - target_squads: "Squads to enrich"
  optional:
    - source_context: "Description of source for attribution"

outputs:
  primary:
    - enriched_files: "List of reference files modified with change counts"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold-enrichment
  task_name: Enrichment — Merge Insights into Reference Files
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Operational
  input:
  - '{''gold_summary'': ''Ranked insights from Phase 2''}'
  - '{''classified_insights'': ''All insights classified as NEW/KNOWN/CONTRADICTS/ENRICHES''}'
  - '{''expert_slug'': ''Expert identifier''}'
  - '{''target_squads'': ''Squads to enrich''}'
  - '{''source_context'': ''Description of source for attribution''}'
  output:
  - '{''enriched_files'': ''List of reference files modified with change counts''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: List of reference files modified with change counts'
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


# Task: Enrichment -- Merge Insights into Reference Files

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-expert-gold-enrichment` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `extract-expert-gold` (orchestrator stub)
- **Sequence:** Phase 4 of 5
- **Previous Task:** `extract-expert-gold-filter`
- **Next Task:** `extract-expert-gold-validation`

## Purpose

Write new insights into the correct squad reference files. Route each insight by domain, apply append-only merge strategy, and enforce squad agnosticism before any write operation.

## Prerequisites

- `gold_summary` must have been confirmed by user in Phase 2
- `classified_insights` must contain at least 1 NEW or ENRICHES insight
- `target_squads` must be valid squad names with existing data directories

## Step 3.1: Route to Target Files

```yaml
routing_rules:
  # Each insight goes to the squad reference file that matches its domain
  - if insight.category in [framework, tactic, philosophy] AND squad == "copy":
      target: "squads/copy/data/references/{expert_slug}-copy-analysis.yaml"
  - if insight.category in [metric, tactic] AND squad == "traffic-masters":
      target: "squads/traffic-masters/data/references/{expert_slug}-*.yaml"
  - if insight relates to offer/pricing/funnel architecture:
      target: "squads/hormozi/data/references/{expert_slug}-*.yaml"

  # Create new file if no existing reference matches
  - if no matching file exists:
      create: "squads/{squad}/data/references/{expert_slug}-{topic}-analysis.yaml"
```

## Step 3.2: Merge Strategy

```yaml
merge_rules:
  # NEVER overwrite existing data
  strategy: "append_and_enrich"

  for NEW insights:
    - Add as new section or append to matching section
    - Include source attribution: "Source: {source_context}, {timestamp}"
    - Include confidence marker

  for ENRICHES insights:
    - Add detail under existing section
    - Mark as "Enrichment from: {source_context}"
    - Preserve original data intact

  for CONTRADICTS insights:
    - Add both versions with clear labels
    - Mark: "CONFLICT -- requires human resolution"
    - Include timestamps and confidence for both

  formatting:
    - Follow existing file structure (YAML or Markdown)
    - Maintain alphabetical/logical section ordering
    - Keep line count manageable (warn if file > 1000 lines)
```

## Step 3.3: Squad Agnosticism Check

```yaml
before_writing:
  scan_for_violations:
    - Business names (company, product, brand names)
    - Specific pricing (real prices of specific products)
    - Client/customer names
    - Internal project references

  if violation found:
    - Generalize: "specific low-ticket price" -> "low-ticket front (price-range placeholder)"
    - Remove: specific client names -> "case study in {niche}"
    - Flag: anything that cannot be generalized
```

## Elicitation Point (Conditional)

If CONTRADICTS insights exist, present them to the user:

> "Found contradictions between new and existing data. Which version to keep?"

**Default:** Flag both versions in the file.

## Output

Pass `enriched_files` (list of modified file paths with line counts) to the next task (`extract-expert-gold-validation`).

---

_Task Version: 1.0.0_
_Parent: extract-expert-gold_
_Phase: 3 -- Enrichment_

## Acceptance Criteria

- [ ] Output artifact produced: List of reference files modified with change counts
- [ ] Task output validated against quality standards
