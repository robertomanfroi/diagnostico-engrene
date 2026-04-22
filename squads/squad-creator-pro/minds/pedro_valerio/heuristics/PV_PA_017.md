---
id: "PV_PA_017"
title: "Variance as a Feature (Six Sigma Agent Paradox)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Stochastic Operations"
  - "Six Sigma Trap"
pipeline_instances:
  - "quality-control"
sys_tension:
  - tension_with: "PV_PA_016 (Repeatability as Quality)"
    resolution: "Repeatability applies to Workers (deterministic systems). Agents operate in creative variance zones where stochasticity is generative. Route rigid requirements to Workers; embrace variance for Agents."
---

# PV_PA_017 - Variance as a Feature

**Type:** Decision Heuristic
**Phase:** 5 (Optimization / Quality Gate)
**Agent:** @hybridOps:process-architect

## Purpose

Do not apply Six Sigma variance reduction algorithms to Agents. Agent variance (stochasticity) is not a defect; it is a feature that enables creative and contextual generation. If your process requires zero variance (3.4 defects per million), use a Worker, not an Agent.

## Configuration

```yaml
PV_PA_017:
  name: "Variance as a Feature"
  phase: 5

  veto_conditions:
    - condition: "applying_DMAIC_to_eliminate_agent_variance == true"
      action: "VETO - You are measuring the wrong tool with the wrong ruler."
```

## Application

**Process:** When operations complain that the AI "isn't generating exactly the same text every time", audit the task. Do they truly need rigid execution? If yes, route it to code. If they need generation, accept the variance.

## Decision Tree

```
IF (Task demands 100% rigid Boolean conformity without deviation) 
THEN EXECUTOR = WORKER
ELSE IF (Task benefits from emergent variation and empathy matching)
THEN EXECUTOR = AGENT.
```

## Failure Modes

### Prompt Choking (Defensive Prompting)
- **Manifestation:** Injecting 50 strict guardrails into a Prompt to eliminate any "creative variation", effectively Castrating the Agent into becoming an extremely slow, expensive, and fragile Worker script.

---

## Validation

✓ **Paradox Identified:** Six Sigma methodology (minimize variance) vs. Agent generative capacity (requires variance).

✓ **Tension Resolution:** Route deterministic tasks (100% rigid conformity) to Workers. Route generative tasks to Agents and embrace stochasticity.

✓ **Cross-reference:** Relationship with PV_PA_016 (Repeatability) clarified in sys_tension field.

✓ **Heuristic Integrity:** This rule prevents organizational antipatterns (over-engineering Agents with guardrails, turning them into expensive Workers).
