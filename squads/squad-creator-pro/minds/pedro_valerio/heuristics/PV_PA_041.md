---
id: "PV_PA_041"
title: "Fragile Automation Ejection (Jeitinho Rule)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Worker Evaluation"
  - "Structural Integrity"
pipeline_instances:
  - "process-optimization"
sys_tension:
  tension_with: "PV_PA_003 (Pragmatic Flexibility)"
  resolution: "Workers enforce deterministic fail-fast; Agents handle contextual interpretation. No blending."
---

# PV_PA_041 - Fragile Automation Ejection

**Type:** Decision Heuristic
**Phase:** 5 (Optimization)
**Agent:** @hybridOps:process-architect

## Purpose

A Worker should execute deterministically on clean rules or fail aggressively. If a Developer programs a Worker script to try and "creatively guess" or "dar um jeitinho" around badly formatted input payload data, the logic is fatally compromised. Ensure Workers fail fast to route anomalies properly.

## Configuration

```yaml
PV_PA_041:
  name: "Fragile Automation Ejection"
  phase: 5

  veto_conditions:
    - condition: "worker_contains_complex_guessing_algorithms_for_badly_structured_inputs == true"
      action: "VETO - A Worker must fail confidently on bad data. Use an Agent if inputs require interpretation."
```

## Application

**Process:** If the API webhook payload gets messy and the execution fails, do not write 100 extra lines of rigid regex string manipulation to "guess" the intention. Bounce standard errors to a Semantic Agent to clean up, or fail the run entirely so data isn't corrupted downstream.

## Decision Tree

```
IF (Worker logic involves extensive contextual guessing or patching unformatted text) 
THEN ASSIGN TO AGENT.
```

## Failure Modes

### Structural Spaghetti (O Jeitinho)
- **Trigger:** Programmers trying to artificially make a static Worker "smart" by cramming infinite edge-case IF/THEN loops for misspelled user inputs. Results in untraceable and silent data routing failures.

---

## Validation

✓ **Paradox Identified:** Rigor (fail-fast on bad data) vs. Pragmatism (flexible correction logic)
✓ **Tension Resolution:** Clear boundary — Workers = deterministic rejection; Agents = interpretation
✓ **Fail-Safe Mechanism:** Invalid payloads route to semantic agents, never silently processed
✓ **No Jeitinho Tolerance:** Zero compromise on data integrity through guessing algorithms
