---
task-id: refresh-registry
name: "Refresh Squad Registry"
version: 3.0.0
execution_type: Orchestrator
model: Haiku
model_rationale: "Orchestrator stub -- delegates to 3 atomic sub-tasks. Haiku for routing."
haiku_eligible: true
note: "Decomposed from v2.0.0 monolith (424 lines, 6 steps) into 3 atomic tasks."
estimated-time: 15-30 min
complexity: medium

inputs:
  required: []
  optional:
    - squads_path: "Base path to scan (default: squads/)"
    - preserve_manual: "Keep manual highlights, quality_reference (default: true)"
    - update_gaps: "Re-analyze gaps (default: false)"

outputs:
  primary:
    - registry_file: "Updated squads/squad-creator-pro/data/squad-registry.yaml"

worker_script: "scripts/refresh-registry.py"
elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: refresh-registry
  task_name: Refresh Squad Registry
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 15-30m
  domain: Operational
  input:
  - '{''squads_path'': ''Base path to scan (default: squads/)''}'
  - '{''preserve_manual'': ''Keep manual highlights, quality_reference (default: true)''}'
  - '{''update_gaps'': ''Re-analyze gaps (default: false)''}'
  output:
  - '{''registry_file'': ''Updated squads/squad-creator-pro/data/squad-registry.yaml''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - All squads in squads/ are in registry
  - All registry entries have valid paths
  - domain_index has no orphan entries
  - YAML is valid and parseable
  - No duplicate keywords pointing to wrong squads
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Refresh Squad Registry

**Command:** `*refresh-registry`

> **Architecture:** Hybrid (Python script for deterministic counts + LLM for semantic enrichment)

---

## Pipeline (3 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `refresh-registry-scan` | Run Script & Collect Data | 5 min |
| 2 | `refresh-registry-enrich` | LLM Enrichment & Build Entries | 10 min |
| 3 | `refresh-registry-write` | Domain Index, Write & Validate | 5 min |

---

## Execution Flow

```
refresh-registry-scan
  | script_output (JSON with counts, metadata, agent names)
  v
refresh-registry-enrich
  | enriched_entries (domain, keywords, highlights, example_use)
  v
refresh-registry-write
  | registry_file (FINAL OUTPUT)
  v
[DONE]
```

---

## Triggers

| Trigger | When |
|---------|------|
| Manual | `*refresh-registry` command |
| Post-create | After `*create-squad` completes |
| Pre-commit hook | Changes to `squads/*/config.yaml` |
| Auto-refresh | Registry older than 24 hours (if enabled) |

---

## Worker Script

```bash
python3 squads/squad-creator-pro/scripts/refresh-registry.py --output json --registry-format
```

---

## Output

```yaml
output:
  file: "squads/squad-creator-pro/data/squad-registry.yaml"
  console: |
    Registry updated successfully!
    Squads: {total} ({new} new, {updated} updated)
    Domains covered: {domain_count}
    Gaps remaining: {gap_count}
```

---

## Validation

- [ ] All squads in squads/ are in registry
- [ ] All registry entries have valid paths
- [ ] domain_index has no orphan entries
- [ ] YAML is valid and parseable
- [ ] No duplicate keywords pointing to wrong squads

---

_Task Version: 3.0.0_
_Created: 2026-02-01 | Decomposed: 2026-03-26_

## Task Anatomy

- **Executor:** Agent
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Updated squads/squad-creator-pro/data/squad-registry.yaml
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Updated squads/squad-creator-pro/data/squad-registry.yaml
- [ ] Task output validated against quality standards
