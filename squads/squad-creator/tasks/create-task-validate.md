# Task: Validate and Save Task

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-task-validate
name: Validate and Save Task
category: task-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Run SC_TSK_001 quality gate on the generated task file,
  fix any blocking issues (max 2 iterations), and save
  the validated task file to the squad's tasks directory.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_validate
Output: artifact::create_task_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Ensure the generated task file meets quality standards by running the SC_TSK_001 quality gate, iterating on fixes for blocking issues, and persisting the validated file. This is the final quality checkpoint before the task becomes part of the squad.

## Prerequisites

- [ ] Task file content generated (from create-task-generate)
- [ ] `data/decision-heuristics-framework.md` accessible
- [ ] `data/quality-dimensions-framework.md` accessible
- [ ] Write permissions for `squads/{squad_name}/tasks/`

## Inputs

```yaml
inputs:
  - name: task_file_content
    type: string
    required: true
    source: previous_task
    description: "Generated task file markdown content"

  - name: squad_name
    type: string
    required: true
    source: previous_task
    description: "Target squad identifier"

  - name: task_id
    type: string
    required: true
    source: previous_task
    description: "Task identifier (kebab-case)"

  - name: complexity
    type: enum
    required: false
    source: previous_task
    values: ["simple", "complex"]
    default: "simple"
```

## Workflow / Steps

### Step 1: Run Quality Gate SC_TSK_001

```yaml
quality_gate:
  heuristic_id: SC_TSK_001
  name: "Task Quality Gate"
  blocking: true

  blocking_requirements:
    task_anatomy_complete:
      - id_defined: true
      - purpose_clear: true
      - executor_assigned: true
      - inputs_defined: ">= 1"
      - preconditions_listed: ">= 1"
      - steps_defined: ">= 3"
      - outputs_defined: ">= 1"
      - validation_criteria: ">= 1"
    lines:
      simple: ">= 300"
      complex: ">= 500"
    examples: ">= 1"
    error_handling: "defined"

  scoring:
    dimensions:
      - name: Completeness
        weight: 0.25
        check: "All 8 fields present"
      - name: Clarity
        weight: 0.20
        check: "Steps are unambiguous"
      - name: Executor_fit
        weight: 0.20
        check: "Right executor assigned"
      - name: Guardrails
        weight: 0.15
        check: "Appropriate safeguards"
      - name: Examples
        weight: 0.10
        check: "Realistic examples"
      - name: Documentation
        weight: 0.10
        check: "Well-documented"

  threshold: 7.0

  veto_conditions:
    - anatomy_incomplete: "Missing required Task Anatomy fields"
    - no_validation: "No validation criteria defined"
    - wrong_executor: "Executor doesn't match task type"
```

### Step 2: Fix Blocking Issues (if any)

```yaml
fix_blocking:
  max_iterations: 2

  for_each_failure:
    - identify: "What's missing"
    - source: "Where to get it (elicit or derive)"
    - fix: "Add the content"

  common_fixes:
    missing_anatomy_field:
      - "Return to anatomy elicitation for that field"
      - "Elicit missing information"
    too_short:
      - "Add more detail to steps"
      - "Expand examples"
      - "Add error handling scenarios"
    unclear_steps:
      - "Break into smaller steps"
      - "Add expected outputs per step"
      - "Add decision criteria"
```

### Step 3: Save Task File

```yaml
save_task:
  path: "squads/{squad_name}/tasks/{task_id}.md"
  post_save:
    - verify_markdown_valid
    - update_agent_dependencies
    - log_creation
```

### Step 4: Present Summary

```yaml
present_summary:
  task_created:
    id: "{task_id}"
    purpose: "{purpose}"
    executor: "{executor type}"
    file: "squads/{squad_name}/tasks/{task_id}.md"
    lines: N
  quality:
    score: "X.X/10"
    status: "PASS"
```

## Output

```yaml
output:
  name: validated_task
  format: yaml
  structure:
    quality_score: "X.X/10"
    blocking_requirements: "ALL PASS"
    task_file: "squads/{squad_name}/tasks/{task_id}.md"
    lines: N
    status: "PASS | FAIL"
    fix_iterations: N
```

## Acceptance Criteria

- [ ] SC_TSK_001 quality gate passes (score >= 7.0)
- [ ] No veto conditions triggered
- [ ] All blocking requirements satisfied
- [ ] Task file saved to correct path
- [ ] Markdown is valid
- [ ] Summary presented with score and status

## Veto Conditions

- SC_TSK_001 score < 7.0 after 2 fix iterations
- Any veto condition (anatomy_incomplete, no_validation, wrong_executor) persists
- File cannot be saved to target path

## Related Documents

- `data/decision-heuristics-framework.md` -- Quality gate logic
- `data/quality-dimensions-framework.md` -- Scoring dimensions
- `create-task-generate.md` -- Prerequisite (provides file content)
- `create-task-register.md` -- Next step (registers in config)
- `create-task.md` -- Parent composed task

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 4_
