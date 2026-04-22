# Task: Define Task Anatomy

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-anatomy` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-task-anatomy
name: Define Task Anatomy
category: task-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Define all 8 required Task Anatomy fields through structured
  elicitation: ID, Purpose, Executor, Inputs, Preconditions,
  Steps, Outputs, and Validation.
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_anatomy
Output: artifact::create_task_anatomy
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Populate the 8 mandatory Task Anatomy fields through interactive elicitation, producing a complete task specification ready for file generation. This phase transforms the classification output into a fully defined task structure.

## Prerequisites

- [ ] Phase 0 classification complete (output: `phase_0_classification`)
- [ ] Executor type already assigned
- [ ] Target squad validated

## Inputs

```yaml
inputs:
  - name: phase_0_classification
    type: object
    required: true
    source: previous_task
    description: "Output from create-task-classify"

  - name: task_purpose
    type: string
    required: true
    source: user
    description: "What the task should accomplish"

  - name: complexity
    type: enum
    required: false
    source: user
    values: ["simple", "complex"]
    default: "simple"
```

## Workflow / Steps

### Step 1: Define Field 1-2 (ID and Purpose)

```yaml
elicit_identity:
  field_1_id:
    question: "What should be the task ID? (kebab-case)"
    example: "generate-sales-page"
    validation: "Must be unique within squad"

  field_2_purpose:
    question: "What is the purpose of this task?"
    prompt: "Complete: 'This task exists to...'"
    example: "Generate high-converting sales page copy following proven frameworks"
    requirements:
      - "Clear goal statement"
      - "Value proposition"
      - "Measurable outcome if possible"
```

### Step 2: Define Field 3 (Executor)

Use result from Phase 0 classification. Confirm with user.

```yaml
elicit_executor:
  present: "Based on analysis, I recommend: {executor}"
  rationale: "{executor_rationale}"
  question: "Does this executor assignment make sense?"
  if_disagree:
    options:
      - "Human - I need full human control"
      - "Agent - Let AI handle it fully"
      - "Hybrid - AI drafts, I review"
      - "Worker - It's purely mechanical"
  guardrails_prompt:
    - "What guardrails should be in place for this executor?"
```

### Step 3: Define Field 4 (Inputs)

```yaml
elicit_inputs:
  question: "What inputs does this task need?"
  for_each_input:
    - "What is the input name?"
    - "What type is it? (string, file, object, list)"
    - "Is it required or optional?"
    - "Where does it come from? (user, previous task, database, API)"
    - "How should it be validated?"
  minimum_inputs: 1
  document_all: true
```

### Step 4: Define Field 5 (Preconditions)

```yaml
elicit_preconditions:
  question: "What must be true before this task can start?"
  categories:
    data_prerequisites:
      - "What data must exist?"
      - "What research must be done?"
    system_prerequisites:
      - "What tools or systems must be available?"
      - "What permissions are needed?"
    sequence_prerequisites:
      - "What tasks must complete first?"
      - "What agent context is required?"
  format_as_checklist: true
```

### Step 5: Define Field 6 (Steps)

```yaml
elicit_steps:
  question: "Let's break down the workflow. What are the main steps?"
  for_each_step:
    - name: "Step name (action verb)"
    - action: "What exactly should happen"
    - elicit: "Does this step need user input? (true/false)"
    - output: "What does this step produce"
    - conditions: "Any conditional logic"
  structure_guidance:
    simple_task:
      - "3-7 steps"
      - "Linear flow"
      - "Clear action per step"
    complex_task:
      - "7-15 steps"
      - "May have branches"
      - "Checkpoints between sections"
```

### Step 6: Define Field 7 (Outputs)

```yaml
elicit_outputs:
  question: "What does this task produce?"
  for_each_output:
    - name: "Output name"
    - format: "markdown | yaml | json | file"
    - location: "Where to save (pattern allowed)"
    - structure: "What sections/fields"
  primary_output:
    required: true
    must_have:
      - "Clear filename pattern"
      - "Defined structure"
      - "Quality criteria"
  secondary_outputs:
    optional: true
```

### Step 7: Define Field 8 (Validation)

```yaml
elicit_validation:
  question: "How do we know this task completed successfully?"
  categories:
    completeness: "Are all required sections present?"
    quality: "Does output meet quality standards?"
    domain_specific: "Does it include required domain elements?"
    format: "Is the structure correct?"
  blocking_vs_warning:
    blocking: "Failures that prevent task from completing"
    warning: "Issues that should be noted but don't block"
```

### Step 8: Run Checkpoint SC_ANA_001

```yaml
checkpoint:
  heuristic_id: SC_ANA_001
  name: "Task Anatomy Complete"
  blocking: true
  criteria:
    - field_1_id: "defined and unique"
    - field_2_purpose: "clear and specific"
    - field_3_executor: "assigned with rationale"
    - field_4_inputs: "at least 1 defined"
    - field_5_preconditions: "checklist created"
    - field_6_steps: "3+ steps defined"
    - field_7_outputs: "primary output defined"
    - field_8_validation: "criteria defined"
```

## Output

```yaml
output:
  name: task_anatomy_complete
  format: yaml
  structure:
    id: "{task-id}"
    purpose: "{purpose statement}"
    executor:
      type: "{Worker|Agent|Hybrid|Human}"
      rationale: "{why}"
    inputs: [{name, type, required, source}]
    preconditions: ["checklist items"]
    steps: [{name, action, elicit, output}]
    outputs: [{name, format, location, structure}]
    validation: [{criterion, type}]
    checkpoint_SC_ANA_001: "PASS"
```

## Acceptance Criteria

- [ ] All 8 Task Anatomy fields are defined
- [ ] Each field has concrete values (no placeholders)
- [ ] Steps count >= 3
- [ ] At least 1 input defined
- [ ] Primary output has filename pattern and structure
- [ ] Validation criteria distinguish blocking vs warning
- [ ] Checkpoint SC_ANA_001 passes

## Veto Conditions

- Any of the 8 fields left undefined
- SC_ANA_001 checkpoint fails
- Steps fewer than 3
- No validation criteria defined

## Related Documents

- `create-task-classify.md` -- Prerequisite (provides executor assignment)
- `create-task-executor.md` -- Next step (designs guardrails)
- `create-task.md` -- Parent composed task
- `data/executor-matrix-framework.md` -- Executor profiles

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 1_
