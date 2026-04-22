# Task: Classify Workflow Operation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-workflow-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-workflow-classify
name: Classify Workflow Operation
category: workflow-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Validate that the operation meets workflow criteria (3+ phases,
  multiple agents, intermediate checkpoints), collect workflow
  identity (name, id, duration, scope), and redirect to
  *create-task if classification fails.
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_workflow_classify
Output: artifact::create_workflow_classify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Determine whether a requested operation qualifies as a multi-phase workflow or should be an atomic task instead. Collect the workflow identity fields (name, id, duration, description, scope) through structured elicitation. This is the gate that prevents misclassification -- if it fails, no subsequent phases execute.

## Prerequisites

- [ ] Target squad exists at `squads/{squad_name}/`
- [ ] squad-chief agent is active
- [ ] Write permissions for `squads/{squad_name}/workflows/`
- [ ] Apply `squads/squad-creator/protocols/ai-first-governance.md`

## Inputs

```yaml
inputs:
  - name: workflow_purpose
    type: string
    required: true
    source: user
    description: "What the workflow should accomplish"

  - name: squad_name
    type: string
    required: true
    source: user
    description: "Target squad identifier"
```

## Workflow / Steps

### Step 1: Validate Workflow Criteria

**Actions:**

```yaml
validate_criteria:
  check_each:
    - has_3plus_phases: "How many distinct phases?"
    - multiple_agents: "How many agents involved?"
    - spans_multiple_days: "Expected duration?"
    - needs_checkpoints: "Validation points between phases?"
    - output_feeds_next: "Does phase output feed next phase?"

  decision:
    if_any_true: "Workflow is appropriate"
    if_all_false: "Redirect to *create-task"
```

**Elicitation:**

```yaml
elicit_validation:
  questions:
    - "Does this operation have 3+ distinct phases?"
    - "Are multiple agents involved?"
    - "Will it span multiple days or sessions?"
    - "Do you need validation checkpoints between phases?"

  if_all_no:
    action: "This should be a TASK, not a workflow."
    redirect: "*create-task"
```

### Step 2: Define Workflow Identity

**Elicitation:**

```yaml
elicit_identity:
  workflow_name:
    question: "What is the workflow name? (human-readable)"
    example: "High-Ticket Sales Pipeline"

  workflow_id:
    question: "What is the workflow ID? (kebab-case)"
    example: "high-ticket-sales"
    validation: "Must be unique within squad"

  duration:
    question: "What is the expected duration?"
    example: "7-10 days"

  description:
    question: "What does this workflow accomplish?"
    example: "Orchestrates the complete sales pipeline from lead capture to close"

  phase_count:
    question: "How many phases will this workflow have? (minimum 3)"
    validation: ">= 3"
```

### Step 3: Define Scope

**Elicitation:**

```yaml
elicit_scope:
  primary_goal:
    question: "What is the primary goal of this workflow?"

  target_user:
    question: "Who will execute this workflow?"

  use_cases:
    question: "What are 3-5 specific use cases for this workflow?"

  decision_criteria:
    question: "When should someone choose this workflow over alternatives?"
```

### Step 4: AI-First Governance Gate

```yaml
governance_gate:
  checks:
    - "Map Existing -> Gap -> Decision before phase design"
    - "Validate canonical references for tasks/checklists/data"
    - "Explicitly track unresolved items and contradictions"
    - "Avoid absolute completion claims when dependencies are not fully implemented"
```

## Output

```yaml
output:
  name: phase_0_classification
  format: yaml
  structure:
    workflow_name: "{workflow-name}"
    workflow_id: "{workflow-id}"
    duration: "{duration}"
    description: "{description}"
    squad_name: "{squad-name}"
    phase_count: "{count}"
    criteria_validated: true
    scope:
      primary_goal: "{goal}"
      target_user: "{user}"
      use_cases: []
      decision_criteria: "{criteria}"
```

## Acceptance Criteria

- [ ] Workflow criteria validated (at least one criterion is true)
- [ ] Operation redirected to *create-task if no criteria met
- [ ] Workflow name, id, duration, and description collected
- [ ] Phase count is >= 3
- [ ] Scope defined (primary goal, target user, use cases)
- [ ] AI-First governance gate checked

## Veto Conditions

- All workflow criteria are false and user proceeds anyway
- Phase count < 3 and not redirected to *create-task
- Workflow ID is not unique within squad
- Target squad does not exist

## Related Documents

- `create-workflow.md` -- Parent composed task
- `create-task.md` -- Alternative if classification yields Task
- `data/tier-system-framework.md` -- Used in next phase (phases)
- `protocols/ai-first-governance.md` -- Governance protocol

---

_Task Version: 1.0.0_
_Extracted from: create-workflow.md PHASE 0_
