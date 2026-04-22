---
id: "PV_PA_004"
title: "Zero-Cost Determinism (Worker First)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Worker Profile"
  - "Cost-Optimization"
pipeline_instances:
  - "process-automation"
  - "task-allocation"
sys_tension:
  tension_with: "PV_PA_005 (Directed Stochasticity) — Variance as a Feature"
  resolution: "Layered Executor Architecture — Workers handle deterministic core paths with Agent/Human fallback layers for edge cases discovered post-deployment"
---

# PV_PA_004 - Zero-Cost Determinism (Worker First)

**Type:** Decision Heuristic
**Phase:** 3 (Executor Selection)
**Agent:** @hybridOps:executor-designer
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Enforce the priorization of Workers (deterministic scripts/RPA) over Agents or Humans whenever a process can be reduced to strict Boolean logic. Prevents wasting API tokens, latency, and generating unwanted variance on mathematically rigid tasks.

## Configuration

```yaml
PV_PA_004:
  name: "Zero-Cost Determinism"
  phase: 3
  pattern_reference: "HO-PP-003"

  weights:
    task_is_deterministic: 1.0
    task_volume_scale: 0.8

  thresholds:
    determinism_score: 0.9

  veto_conditions:
    - condition: "task_is_deterministic = true AND executor_type IN ['Human', 'Agent']"
      action: "VETO - Assign to Worker immediately"

  output:
    type: "decision"
    values: ["ROUTE_TO_WORKER", "EVALUATE_FOR_AGENT", "VETO"]
```

## Application

**Input:** Data processing tasks, classification tasks, structured data I/O
**Process:** Determine if the logic can be hardcoded (if/else, regex) instead of inferred.
**Output:** ROUTE_TO_WORKER | EVALUATE_FOR_AGENT | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (task logic is strictly 'if X then Y else Z' with no ambiguity)
    THEN ROUTE_TO_WORKER

SECONDARY BRANCH:
  ELSE IF (input format is strict and volume is extreme)
    THEN ROUTE_TO_WORKER (with fallback mechanism)

TERTIARY BRANCH:
  ELSE IF (task requires interpreting unstructured text or fuzzy matching)
    THEN EVALUATE_FOR_AGENT

TERMINATION: Any task requiring exact identical outputs for identical inputs is a Worker task.
CONSTRAINT: NEVER use an Agent to parse standard JSON or extract Regex-friendly strings.
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Determinism Level | 1.0 | ≥0.9 | Is the logic completely rigid and predictable? |
| Volume/Scale | 0.8 | ≥0.5 | High frequency warrants infrastructure coding. |
| Cost Risk | 0.7 | ≥0.6 | Tokens wasted vs Free CPU processing. |

## Confidence Requirements

- **High commitment decisions:** 100% confidence required that no ambiguous edge-cases exist in the main flow before hardcoding a Worker.
- **Tactical decisions:** Scripts can be deployed rapidly if fallback layers are assigned to Humans.

## Performance Metrics

```yaml
performance:
  decision_speed: "Milliseconds (execution phase)"
  accuracy_rate: "100% (true determinism)"
  confidence_level: "100% (removes stochastic hallucination entirely)"
  resource_efficiency: 10/10 (Margin protection)
```

## Failure Modes

### AI-Washing (The Coward)
- **Trigger:** Using GPT-4 or Claude to "clean up data" or "sort lists" because writing a script feels like too much work.
- **Manifestation:** Soaring API costs and occasional format regressions (LLM hallucinating numbers).
- **Detection:** Large token volume for tasks producing simple boolean or tabular outputs.
- **Recovery:** Swap the Agent step for a Python/RPA Worker.
- **Prevention:** Pre-filter structured data using standard code before it ever touches an AI Agent.

### Over-Engineering the Edge (The Zealot)
- **Trigger:** Attempting to force fuzzy language tasks into thousands of if/else rules to avoid paying for an Agent.
- **Manifestation:** Script breaks weekly; maintenance costs exceed AI API costs.
- **Recovery:** Demote the rule-based Engine; use an Agent for the fuzzy layer and a Worker for the clean layer.

## Behavioral Evidence

**Example:** Lead Triage Optimization
- **Context:** An operation was using LLMs to read CNPJs and segment leads by company size.
- **Information Available:** Cost scaling linearly with leads, 4-second latency per lead.
- **Heuristic Application:** Substituted the Agent with a direct API Worker (Receita Federal query + hardcoded math).
- **Outcome:** Latency dropped to 110ms. Cost fell by 99%. Hallucination risk zeroed.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 3:

```yaml
checkpoint:
  id: "worker-first-triage"
  heuristic: PV_PA_004
  phase: 3

  criteria:
    - metric: "determinism_score"
      threshold: 0.9
      operator: ">="
    - metric: "requires_inference"
      required: false

  veto_conditions:
    - condition: "requires_inference == false AND assigned_executor != 'Worker'"
      action: "HALT - Task must be assigned to Worker"

  validation_questions:
    - "Can this logic be expressed entirely in regular code without AI?"
    - "Is absolute consistency mathematical rather than semantic?"

  pass_action: "Assign Worker Executor"
  fail_action: "Proceed to Agent/Human Evaluation"
```

---

## Validation

- **Paradox Identified:** Heuristic requires 100% determinism confidence (§ Confidence Requirements, line 85) yet real-world production discovers unpredictable edge cases. Over-applying to fuzzy tasks (The Zealot failure mode) replicates the cost problem it solves.
- **Resolution Applied:** Layered Executor Architecture acknowledges core deterministic paths (Worker-assigned) with mandatory fallback layers (Agent/Human) for anomalies discovered post-deployment.
- **Checksum:** PV_PA_004 + sys_tension validation ✓

---

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part I
