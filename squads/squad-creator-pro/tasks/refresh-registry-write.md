---
task-id: refresh-registry-write
name: "Domain Index, Write & Validate"
version: 1.0.0
execution_type: Worker
model: Haiku
model_rationale: "File writing and YAML validation are deterministic operations."
haiku_eligible: true
estimated-time: 5 min
complexity: low

inputs:
  required:
    - enriched_entries: "Squad entries from Phase 2"
  optional:
    - update_gaps: "Re-analyze gaps (default: false)"

outputs:
  primary:
    - registry_file: "squads/squad-creator-pro/data/squad-registry.yaml"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: refresh-registry-write
  task_name: Domain Index, Write & Validate
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 5m
  domain: Operational
  input:
  - '{''enriched_entries'': ''Squad entries from Phase 2''}'
  - '{''update_gaps'': ''Re-analyze gaps (default: false)''}'
  output:
  - '{''registry_file'': ''squads/squad-creator-pro/data/squad-registry.yaml''}'
  action_items:
  - Update Domain Index
  - Update Gaps Analysis (if enabled)
  - Write Registry File
  - Validate Output
  - Console Summary
  acceptance_criteria:
  - Domain index updated with all mappings
  - YAML file written and valid
  - No duplicate squad names
  - All paths verified to exist
  - Console summary displayed
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
  Domain: Strategic
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Domain Index, Write & Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `refresh-registry-write` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

- **Parent Task:** `refresh-registry` (orchestrator stub)
- **Sequence:** Phase 3 of 3
- **Previous Task:** `refresh-registry-enrich`
- **Next Task:** None (final phase)

## Purpose

Update the domain index, write the complete registry file, and validate structural integrity.

## Workflow / Steps

### Step 1: Update Domain Index

```yaml
update_domain_index:
  for_each_squad:
    - Add squad.domain -> squad_name mapping
    - Add each keyword -> squad_name mapping
  handle_conflicts:
    action: "keep both, note in comments"
    example: |
      analytics: ["data", "monitor"]  # Multiple squads cover this
```

### Step 2: Update Gaps Analysis (if enabled)

```yaml
update_gaps:
  known_domains:
    - finance
    - health
    - sales
    - customer_success
    - product_management
    - research
    - real_estate
  for_each_gap:
    check: "Is there now a squad covering this?"
    if_covered: "Remove from gaps"
    if_not_covered: "Keep in gaps"
```

### Step 3: Write Registry File

```yaml
write_registry:
  file: "squads/squad-creator-pro/data/squad-registry.yaml"
  structure:
    metadata:
      version: "1.0.0"
      last_updated: "{current_date}"
      total_squads: "{count}"
      maintainer: "squad-creator"
    squads: "{all_squad_entries}"
    domain_index: "{all_mappings}"
    gaps: "{remaining_gaps}"
    quality_references: "{preserved_from_original}"
    conventions: "{preserved_from_original}"
```

### Step 4: Validate Output

```yaml
validate:
  - "YAML syntax valid"
  - "No duplicate squad names"
  - "All paths exist"
  - "domain_index has no orphan entries"
```

### Step 5: Console Summary

```
Registry updated successfully!

Squads: {total} ({new} new, {updated} updated)
Domains covered: {domain_count}
Gaps remaining: {gap_count}

New squads detected:
- {new_squad_1}

Updated squads:
- {updated_squad_1}: +2 agents, +1 task
```

## Output

```yaml
registry_file: "squads/squad-creator-pro/data/squad-registry.yaml"
```

## Acceptance Criteria

- [ ] Domain index updated with all mappings
- [ ] YAML file written and valid
- [ ] No duplicate squad names
- [ ] All paths verified to exist
- [ ] Console summary displayed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `refresh-registry.md` | Parent orchestrator |
| `refresh-registry-enrich.md` | Previous phase |
