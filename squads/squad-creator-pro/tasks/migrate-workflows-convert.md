<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: migrate-workflows-convert
  task_name: Migrate Workflows -- Convert + Validate
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Convert to YAML
  - Validate
  acceptance_criteria:
  - Create `wf-{workflow-id}.yaml` for each analyzed workflow
  - Fill all required fields (workflow-id, name, version, phases)
  - Map .md sections to YAML phases
  - Preserve all semantic information from original
  - Verify YAML syntax parses without error
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Migrate Workflows -- Convert + Validate

**Task ID:** migrate-workflows-convert
**Parent Task:** `migrate-workflows-to-yaml.md`
**Purpose:** Convert legacy .md workflows to YAML format using template, validate syntax and fields
**Execution Type:** Hybrid
**Model:** `Sonnet`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Migrate Workflows -- Convert + Validate |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | `migration_analysis` from analyze step + `workflow-tmpl.yaml` |
| **output** | `.yaml` workflow files + validation results |
| **action_items** | 2 steps |
| **acceptance_criteria** | All workflows converted, YAML syntax valid, required fields present |

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-MWY-001 | Dry-run output must be reviewed before applying | Generate YAML preview and validate syntax before writing | VETO - BLOCK |

---

## Workflow

### Step 1: Convert to YAML

Use `workflow-tmpl.yaml` as base and fill with extracted data.

**Substeps:**

- [ ] Create `wf-{workflow-id}.yaml` for each analyzed workflow
- [ ] Fill all required fields (workflow-id, name, version, phases)
- [ ] Map .md sections to YAML phases
- [ ] Preserve all semantic information from original

**Example conversion:**

```markdown
# Before (legacy .md):
# Workflow: Mind Research Loop
**Workflow ID:** mind-research-loop
**Purpose:** Research and validate...
## Phase 1: Initial Research
...
```

```yaml
# After (wf-mind-research-loop.yaml):
workflow-id: wf-mind-research-loop
name: Mind Research Loop
version: 2.1.0
description: |
  Research and validate...
phases:
  - id: initial-research
    name: Initial Research
    checkpoint:
      criteria: [...]
```

### Step 2: Validate

- [ ] Verify YAML syntax parses without error
- [ ] Verify required fields present (workflow-id, name, version, phases)
- [ ] Verify each phase has checkpoint
- [ ] Verify references to frameworks/agents are correct
- [ ] Run `*validate-workflow` on each file

---

## Output Contract

```yaml
conversion_results:
  workflows_converted: {n}
  files_created:
    - path: "{path}"
      yaml_valid: true|false
      required_fields: true|false
      phase_checkpoints: true|false
  validation_passed: true|false
```

---

## Completion Criteria

- [ ] All workflows converted to .yaml with wf- prefix
- [ ] YAML syntax validates for all files
- [ ] Required fields present in all files
- [ ] Each phase has checkpoint defined

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `migrate-workflows-archive.md` |
| **Trigger** | All validations pass |
| **Artifact** | `conversion_results` YAML + created .yaml files |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of migrate-workflows-to-yaml.md_

## Acceptance Criteria

- [ ] All workflows converted
- [ ] YAML syntax valid
- [ ] required fields present
