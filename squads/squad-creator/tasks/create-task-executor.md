# Task: Design Executor Profile

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-executor` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-task-executor
name: Design Executor Profile
category: task-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Apply executor-matrix-framework to design guardrails,
  checkpoints, and human review triggers for the assigned
  executor type. Autonomous with confirmation.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_executor
Output: artifact::create_task_executor
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transform the executor assignment from Phase 0 into a complete executor profile with guardrails, checkpoints, and escalation paths. This ensures every task has appropriate safeguards calibrated to its executor type and risk level.

## Prerequisites

- [ ] Phase 0 classification complete (executor type assigned)
- [ ] Phase 1 anatomy complete (steps and outputs defined)
- [ ] `data/executor-matrix-framework.md` is accessible

## Inputs

```yaml
inputs:
  - name: task_anatomy_complete
    type: object
    required: true
    source: previous_task
    description: "Output from create-task-anatomy with all 8 fields"

  - name: phase_0_classification
    type: object
    required: true
    source: previous_task
    description: "Output from create-task-classify with executor assignment"
```

## Workflow / Steps

### Step 1: Design Guardrails

**Apply: executor-matrix-framework.md**

```yaml
design_guardrails:
  based_on_executor: "{executor}"

  guardrail_templates:
    Worker:
      - input_validation: "Strict schema validation"
      - error_handling: "Retry logic, fallback values"
      - logging: "All operations logged"
      - limits: "Rate limits, timeout"

    Agent:
      - confidence_threshold: "Only proceed if >= 0.8"
      - quality_check: "Self-review before output"
      - escalation: "Flag uncertainty for human"
      - audit: "Log reasoning chain"

    Hybrid:
      - draft_quality: "AI must meet min threshold"
      - human_triggers:
        - "confidence < 0.7"
        - "novel scenario detected"
        - "high-stakes output"
      - approval_workflow: "Clear accept/revise/reject"
      - version_control: "Track all versions"

    Human:
      - instructions: "Clear, unambiguous guidance"
      - decision_criteria: "Explicit rules for decisions"
      - escalation_path: "Who to ask when stuck"
      - time_limit: "Expected completion window"
```

### Step 2: Set Checkpoints

```yaml
set_checkpoints:
  for_complex_tasks:
    identify_transitions:
      - "Input validation -> Processing"
      - "Processing -> Output generation"
      - "Draft -> Review"
      - "Review -> Final"

    checkpoint_design:
      - id: "CP-001"
        after_step: 3
        validation: "Inputs validated and analysis complete"
        blocking: true

      - id: "CP-002"
        after_step: 6
        validation: "Draft meets quality threshold"
        blocking: false

  for_simple_tasks:
    checkpoints:
      - "Before output: Validation criteria check"
```

### Step 3: Define Human Review Triggers

For Hybrid and Human executors, identify specific conditions that require human intervention:

- Confidence below threshold
- Novel/unseen scenario
- High-stakes output (client-facing, financial, legal)
- Ambiguous input requiring judgment
- Escalation from automated fallback

### Step 4: Confirm Executor Design

Present the complete executor profile to the user for confirmation:

- Executor type and rationale
- Guardrails list
- Checkpoint count and placement
- Human review triggers (if applicable)
- Fallback chain

## Output

```yaml
output:
  name: executor_profile
  format: yaml
  structure:
    executor: "{type}"
    guardrails:
      - "guardrail description"
    checkpoints:
      count: N
      details:
        - id: "CP-001"
          after_step: N
          validation: "criteria"
          blocking: true|false
    human_review_triggers:
      - "trigger condition"
    fallback:
      type: "{fallback executor}"
      trigger: "condition"
```

## Acceptance Criteria

- [ ] Guardrails match the assigned executor type
- [ ] At least 1 checkpoint for complex tasks
- [ ] Human review triggers defined for Hybrid/Human executors
- [ ] Fallback chain specified
- [ ] Executor profile confirmed by user

## Veto Conditions

- No guardrails defined for the executor type
- Hybrid executor without human review triggers
- No fallback defined

## Related Documents

- `data/executor-matrix-framework.md` -- Executor profiles and patterns
- `create-task-anatomy.md` -- Prerequisite (provides task steps)
- `create-task-generate.md` -- Next step (uses executor profile)
- `create-task.md` -- Parent composed task

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 2_
