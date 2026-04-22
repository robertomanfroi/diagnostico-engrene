# Task: QA Check References

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-check-references` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: qa-check-references
name: QA Check References
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Verify all internal cross-references within a created component.
  Checks that handoff_to targets exist, task references resolve,
  template references resolve, checklist references resolve,
  and dependency chains are valid.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qa_check_references
Output: artifact::qa_check_references
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Ensure every internal reference within the component points to an existing artifact. Broken references cause runtime failures when agents try to follow handoff chains, execute referenced tasks, or load templates. This task catches dangling pointers before delivery.

## Prerequisites

- [ ] qa-check-structure has passed
- [ ] qa-check-schema has passed
- [ ] Component files are readable
- [ ] Squad directory structure is accessible for cross-file lookups

## Inputs

```yaml
inputs:
  - name: created_component
    type: string
    required: true
    description: "Path to created component"

  - name: component_type
    type: enum
    required: true
    values: ["squad", "agent", "task", "workflow", "template"]
    description: "Type of component created"

  - name: schema_result
    type: object
    required: true
    source: qa-check-schema
    description: "Result from schema check (must be PASS)"
```

## Workflow

### Step 1: Extract All References

Scan component files and extract every reference to another artifact:

**For squads:**
- `entry_agent` value --> must match `agents/{value}.md`
- `agents[].id` values --> must match `agents/{id}.md`
- All `handoff_to` targets in agent files --> must match existing agent files
- All task references in agent `commands` or `dependencies` --> must match `tasks/{ref}.md`
- All template references --> must match `templates/{ref}`
- All checklist references --> must match `checklists/{ref}`

**For agents:**
- `handoff_to` targets --> must match sibling agent files
- `dependencies.tasks[]` --> must match `tasks/{name}`
- `dependencies.templates[]` --> must match `templates/{name}`
- `dependencies.checklists[]` --> must match `checklists/{name}`

**For tasks:**
- `source: previous_task` references --> must match sibling task files
- Template references in workflow steps --> must match `templates/{name}`
- Checklist references --> must match `checklists/{name}`
- `Related Documents` links --> must resolve

**For workflows:**
- `phases[].task` --> must match `tasks/{name}.md`
- Output-to-input chains --> output of phase N must match input of phase N+1

### Step 2: Resolve Each Reference

For each extracted reference:
1. Construct the expected file path
2. Check if file exists on disk
3. If file exists, optionally verify it contains the expected identifier (e.g., agent ID matches)
4. Record result: RESOLVED or BROKEN

### Step 3: Detect Orphan Files (Optional, Squads Only)

List all files in the squad directory that are not referenced by any other file. These are potential orphans -- files created but never wired into the squad graph.

### Step 4: Compile Results

```yaml
references_result:
  total_references: N
  resolved: N
  broken: N
  broken_details:
    - source_file: "agents/orchestrator.md"
      reference: "handoff_to: specialist"
      expected_path: "agents/specialist.md"
      status: "BROKEN"
  orphan_files:
    - "templates/unused-template.md"
  verdict: "PASS | FAIL"
```

## Output

```yaml
output:
  name: references_result
  type: object
  description: "Cross-reference validation results"
  passed_to: qa-generate-report
```

## Acceptance Criteria

- [ ] All handoff_to targets validated for existence
- [ ] All task references validated for existence
- [ ] All template references validated for existence
- [ ] All checklist references validated for existence
- [ ] Workflow phase chains validated (output matches next input)
- [ ] Broken references produce FAIL verdict
- [ ] Orphan files detected and reported (non-blocking)

## Veto Conditions

| Condition | Action |
|-----------|--------|
| Entry agent file does not exist | FAIL -- critical reference broken |
| handoff_to target does not exist | FAIL -- agent chain broken |
| Task dependency file missing | FAIL -- workflow will fail at runtime |
| Workflow phase references nonexistent task | FAIL -- workflow is non-executable |

## Related Documents

| Document | Purpose |
|----------|---------|
| `qa-after-creation.md` | Parent orchestrator task |
| `qa-check-schema.md` | Must pass before this task runs |
| `qa-generate-report.md` | Consumes this task's output |
