# Task: QA Check Structure

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-check-structure` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: qa-check-structure
name: QA Check Structure
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Verify directory structure and required files for a created component.
  Covers Phase 0 (Structural Completeness for squads) and Phase 1 Quick Checks
  (file existence, YAML/MD syntax, required metadata) from the original
  qa-after-creation pipeline.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qa_check_structure
Output: artifact::qa_check_structure
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Ensure that a newly created component (squad, agent, task, workflow, template) has the correct directory structure, all required files exist, file syntax is valid, and mandatory metadata fields are present. This is the first and most critical gate -- if structure is wrong, nothing else matters.

## Prerequisites

- [ ] Component has been created by a creation task (`create-squad`, `create-agent`, etc.)
- [ ] Component path is accessible on the filesystem
- [ ] `checklists/squad-structural-completeness.md` accessible (for squad validation)

## Inputs

```yaml
inputs:
  - name: created_component
    type: string
    required: true
    description: "Path to created component"
    example: "squads/my-squad/"

  - name: component_type
    type: enum
    required: true
    values: ["squad", "agent", "task", "workflow", "template"]
    description: "Type of component created"

  - name: creation_task
    type: string
    required: false
    description: "Task that triggered this QA"
    example: "create-squad"
```

## Workflow

### Step 1: Phase 0 -- Structural Completeness (Squads Only)

**Duration:** < 3 seconds | **Blocking:** Yes

Skip this step if `component_type` is not `squad`.

Run these structural checks sequentially. `SC-001` to `SC-007` are blocking; `SC-008` and `SC-009` are contextual lifecycle checks and should not abort validation for operational squads.

| ID | Check | Action | On Fail |
|----|-------|--------|---------|
| SC-001 | config.yaml exists (NOT squad.yaml) | `test -f squads/{name}/config.yaml && ! test -f squads/{name}/squad.yaml` | ABORT |
| SC-002 | entry_agent field present | `grep -q 'entry_agent:' squads/{name}/config.yaml` | ABORT |
| SC-003 | tested field present | `grep -q 'tested:' squads/{name}/config.yaml` | ABORT |
| SC-004 | Entry agent has activation-instructions | Extract entry agent name, verify block exists | ABORT |
| SC-005 | README.md exists | `test -f squads/{name}/README.md` | ABORT |
| SC-006 | CHANGELOG.md exists | `test -f squads/{name}/CHANGELOG.md` | ABORT |
| SC-007 | ARCHITECTURE.md exists | `test -f squads/{name}/ARCHITECTURE.md` | ABORT |
| SC-008 | update task exists | `ls squads/{name}/tasks/update-*.md` | WARN (contextual lifecycle) |
| SC-009 | delete task exists | `ls squads/{name}/tasks/delete-*.md` | WARN (contextual lifecycle) |

### Step 2: Phase 1 -- Quick Checks (All Component Types)

**Duration:** < 5 seconds | **Blocking:** Yes

| ID | Check | On Fail |
|----|-------|---------|
| QC-001 | Component file/directory exists at path | ABORT |
| QC-002 | Valid YAML syntax (for .yaml/.yml files) | ABORT |
| QC-003 | Valid Markdown syntax (unclosed code blocks, broken headers) | WARN |
| QC-004 | Required metadata fields present (see below) | ABORT |

**Required metadata by component type:**

| Type | Required Fields |
|------|----------------|
| squad | name, version, description, entry_agent |
| agent | agent.name, agent.id, persona, commands |
| task | Task ID, Version, Purpose, Inputs, Outputs |
| workflow | Workflow ID, Version, Phases |

### Step 3: Compile Results

Produce a structured result object:

```yaml
structure_result:
  phase_0:
    applicable: true/false
    checks_run: N
    checks_passed: N
    checks_failed: N
    failures: [{id, check, on_fail}]
  phase_1:
    checks_run: N
    checks_passed: N
    checks_failed: N
    warnings: [{id, check, detail}]
    failures: [{id, check, on_fail}]
  verdict: "PASS | ABORT"
  abort_reason: "..." # if verdict is ABORT
```

## Output

```yaml
output:
  name: structure_result
  type: object
  description: "Structured result of directory and file validation"
  passed_to: qa-generate-report
```

## Acceptance Criteria

- [ ] All SC-* checks execute for squad components
- [ ] SC-* checks are skipped for non-squad components
- [ ] All QC-* checks execute for every component type
- [ ] Any ABORT failure halts the pipeline immediately
- [ ] WARN issues are recorded but do not block
- [ ] Result object contains full detail of every check run

## Veto Conditions

| Condition | Action |
|-----------|--------|
| Component path does not exist | ABORT -- cannot validate nonexistent component |
| config.yaml missing for squad | ABORT -- structural prerequisite violated |
| Any SC-* check fails | ABORT -- structural completeness required |
| Required metadata missing | ABORT -- component is incomplete |

## Related Documents

| Document | Purpose |
|----------|---------|
| `checklists/squad-structural-completeness.md` | Reference checklist for SC-* checks |
| `qa-after-creation.md` | Parent orchestrator task |
| `qa-generate-report.md` | Consumes this task's output |
