---
id: "PV_PA_002"
title: "Task-First Assignment (The Invisible Executor)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Process Diagnostics"
  - "Sinkra Framework"
pipeline_instances:
  - "process-mapping"
  - "workflow-design"
sys_tension:
  - tension_with: "PV_KE_069 (O Paradoxo do Executor-First)"
    resolution: "Define task atomicity before assigning executor. Executor becomes swappable ONLY when task constraints are fully explicit and independent of executor type."
---

# PV_PA_002 - Task-First Assignment (The Invisible Executor)

**Type:** Decision Heuristic
**Phase:** 2 (Architecture)
**Agent:** @hybridOps:process-architect
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Process mapping begins with the Task (Atom) definitions, not the Executor. The Executor (Human, Agent, Worker, Clone) is a swappable attribute, preventing the "Invisible Executor" assumption that ruins hybrid process structures.

## Configuration

```yaml
PV_PA_002:
  name: "Task-First Assignment"
  phase: 2
  pattern_reference: "HO-PP-003"

  weights:
    task_isolation_clarity: 0.9
    executor_interchangeability: 0.8

  thresholds:
    high_priority: 0.8
    medium_priority: 0.7

  veto_conditions:
    - condition: "executor_assigned_before_task_defined = true"
      action: "VETO - Map the task inputs and outputs first"
    - condition: "multiple_executors_in_same_atom = true"
      action: "VETO - Split task or define single primary executor"

  output:
    type: "decision"
    values: ["APPROVE", "REWORK", "VETO"]
```

## Application

**Input:** BPMN Diagrams, Process Blueprint, Operational Workflows
**Process:** Ensure tasks are defined atomically before routing to specific executors.
**Output:** APPROVE | REWORK | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (task is fully defined by inputs, constraints, and outputs without assuming an executor)
    THEN map executor attribute → APPROVE

SECONDARY BRANCH:
  ELSE IF (task relies on implicit human intervention/adaptation)
    THEN REWORK to formalize constraints

TERMINATION: Process flowchart explicitly differentiates Worker, Agent, Human, and Clone lanes
CONSTRAINT: NEVER assign "whoever is available" to a task
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Task Isolation | 0.9 | ≥0.8 | Task has clear start and end state without assuming executor? |
| Executor Explicit | 0.9 | ≥1.0 | Is the executor type (Human/Agent/Worker/Clone) strictly defined? |
| Hybrid Visibility | 0.8 | ≥0.7 | Are algorithmic executors visible on the flowchart? |

## Confidence Requirements

- **High commitment decisions:** Requires >90% clarity on the task's atomic boundaries before scaling it to autonomous pipelines.
- **Tactical decisions:** Can proceed with 70% confidence if monitored by a human fallback in production.

## Performance Metrics

```yaml
performance:
  decision_speed: "Seconds (Mental Model check)"
  accuracy_rate: "95% (prevents downstream automation failures)"
  confidence_level: "100% (eliminates Invisible Executor gap)"
  resource_efficiency: 9/10
```

## Failure Modes

### Visual Illusion (The Coward)
- **Trigger:** Approving a traditional BPMN diagram where Agents/Workers live in a generic "System" lane.
- **Manifestation:** Managers think a process is mapped, but algorithmic failures occur silently in production.
- **Detection:** Flowchart looks clean, but errors propagate seamlessly.
- **Recovery:** Force decomposition to the Atom level and label executor types.
- **Prevention:** Ban generic "System" or "AI" swimlanes.

### Granular Paralysis (The Zealot)
- **Trigger:** Defining micro-rules for human-judgment tasks.
- **Manifestation:** Unnecessary documentation overhead for tasks that humans naturally resolve with common sense.
- **Detection:** Process map complexity exceeds execution value.
- **Recovery:** Consolidate micro-tasks into a broader Human task.

## Behavioral Evidence

**Example:** Analyzing a hybrid process diagram with silent AI failures.
- **Context:** An operation uses BPMN but suffers from silent failures when Agents misclassify inputs.
- **Information Available:** Flowchart shows a clean handoff to "The System".
- **Heuristic Application:** Forced the team to map the "System" down to Atoms, revealing an Agent doing a Worker's rigid job.
- **Outcome:** Reassigning the Executor attribute resolved the gap instantly without rewriting the macro algorithm.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 2:

```yaml
checkpoint:
  id: "task-first-validation"
  heuristic: PV_PA_002
  phase: 2

  criteria:
    - metric: "executor_explicitly_defined"
      required: true
    - metric: "task_isolation_clarity"
      threshold: 0.8
      operator: ">="

  veto_conditions:
    - condition: "executor_assigned_before_task"
      action: "HALT - Redefine task atoms"

  validation_questions:
    - "Is the executor explicitly labeled as Human, Agent, Clone, or Worker?"
    - "Can the task be transferred to another executor profile seamlessly?"

  pass_action: "Proceed to Pipeline Documentation"
  fail_action: "Return to Atom Mapping"
```

---

## Validation

✓ **Paradox Identified:** Task-First definition appears contradictory to Executor Interchangeability, but resolves when task constraints (inputs, outputs, constraints, success criteria) are executor-agnostic.

✓ **Tension Resolution:** The heuristic works because it separates task specification (executor-independent) from task routing (executor-dependent). Task atomicity is achieved when rewriting constraints in executor-neutral language is possible.

✓ **SINKRA Alignment:** Enforces Article VI (No Invisible Executors) — all executor assignments must be explicit and traceable to the task definition.

---

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part I
