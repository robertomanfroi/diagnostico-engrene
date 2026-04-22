# Task: Generate Task File

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-generate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-task-generate
name: Generate Task File
category: task-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Generate the task markdown file using task-tmpl.md,
  populate all sections from anatomy and executor profile,
  add usage examples and error handling scenarios.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_generate
Output: artifact::create_task_generate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Produce the final task file by assembling the Task Anatomy fields, executor profile, usage examples, and error handling into a complete markdown document using the squad's task template. This is the assembly phase -- no new decisions, only structured generation.

## Prerequisites

- [ ] Task Anatomy complete (all 8 fields, SC_ANA_001 passed)
- [ ] Executor profile designed (guardrails, checkpoints)
- [ ] `templates/task-tmpl.md` is accessible

## Inputs

```yaml
inputs:
  - name: task_anatomy_complete
    type: object
    required: true
    source: previous_task
    description: "All 8 Task Anatomy fields from create-task-anatomy"

  - name: executor_profile
    type: object
    required: true
    source: previous_task
    description: "Guardrails, checkpoints, triggers from create-task-executor"

  - name: squad_name
    type: string
    required: true
    source: previous_task
    description: "Target squad identifier"
```

## Workflow / Steps

### Step 1: Load and Apply Template

**Template:** `templates/task-tmpl.md`

Generate the task file with these required sections:

```yaml
required_sections:
  header:
    - task_id
    - version: "1.0"
    - purpose
    - orchestrator: "{agent that executes}"
    - mode: "{executor type}"
    - quality_standard

  frameworks:
    - "List frameworks applied"

  overview:
    - "ASCII flow diagram"
    - "Version notes"

  task_anatomy:
    - inputs_table
    - preconditions_checklist
    - steps_detailed
    - outputs_table
    - validation_checklist

  executor_details:
    - guardrails
    - checkpoints
    - human_review_triggers

  examples:
    - "1-3 usage examples"

  error_handling:
    - "Common errors and recovery"

  integration:
    - "Related tasks"
    - "Agent dependencies"
```

### Step 2: Add Usage Examples

```yaml
add_examples:
  minimum: 1
  recommended: 3
  example_structure:
    - scenario: "Brief description"
    - inputs: "What was provided"
    - execution: "Key steps taken"
    - output: "What was produced"
  example_types:
    - "Happy path (normal usage)"
    - "Edge case (unusual inputs)"
    - "Error handling (how errors resolved)"
```

### Step 3: Add Error Handling

```yaml
add_error_handling:
  common_errors:
    - error: "Missing required input"
      cause: "User didn't provide required field"
      handling: "Prompt for missing input"
      recovery: "Continue after input provided"

    - error: "Validation failure"
      cause: "Output doesn't meet criteria"
      handling: "Log specific failures"
      recovery: "Revise and re-validate"

    - error: "Executor timeout"
      cause: "Task took too long"
      handling: "Save partial progress"
      recovery: "Resume from checkpoint"
```

### Step 4: Verify Line Count

```yaml
line_count_check:
  simple_task: ">= 300 lines"
  complex_task: ">= 500 lines"
  action_if_short:
    - "Add more detail to steps"
    - "Expand examples"
    - "Add error handling scenarios"
```

## Output

```yaml
output:
  name: task_file_content
  format: markdown
  location: "squads/{squad_name}/tasks/{task_id}.md"
  structure:
    - Header with metadata
    - Overview with ASCII flow
    - Task Anatomy (8 fields)
    - Executor Details
    - Examples (1-3)
    - Error Handling
    - Integration notes
  quality:
    lines: ">= 300 (simple) or >= 500 (complex)"
    examples: ">= 1"
    error_scenarios: ">= 3"
```

## Acceptance Criteria

- [ ] Task file uses task-tmpl.md structure
- [ ] All 8 Task Anatomy fields populated in the file
- [ ] Executor details section includes guardrails and checkpoints
- [ ] At least 1 usage example included
- [ ] Error handling section covers common failure scenarios
- [ ] Line count meets minimum (300 simple, 500 complex)
- [ ] Valid markdown format

## Veto Conditions

- File generated without all 8 anatomy fields
- No examples included
- No error handling section
- Line count below minimum threshold

## Related Documents

- `templates/task-tmpl.md` -- Task file template
- `create-task-anatomy.md` -- Provides anatomy fields
- `create-task-executor.md` -- Provides executor profile
- `create-task-validate.md` -- Next step (quality gate)
- `create-task.md` -- Parent composed task

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 3_
