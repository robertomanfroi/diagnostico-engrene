---
id: "PV_PA_022"
title: "Primary Validation Coupling (No Auto-Validation)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Quality Control"
  - "Execution Assignment"
pipeline_instances:
  - "quality-gate-design"
sys_tension:
  tension_with: "execution_speed vs validation_integrity"
  resolution: "Decouple validator from generator via Clone/Human intermediary; sacrifice velocity for structural blindness prevention"
---

# PV_PA_022 - Primary Validation Coupling

**Type:** Decision Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

Architectural principle: The executor that generates the output cannot be the sole executor that validates it. Use Clone/Human to validate Agent/Worker. Self-validation is a catastrophic blind spot because LLMs natively suffer from over-confidence in their own rationale.

## Configuration

```yaml
PV_PA_022:
  name: "Primary Validation Coupling"
  phase: 4

  veto_conditions:
    - condition: "generator_executor == validator_executor"
      action: "VETO - Architect a Quality Gate requiring a distinct validator type."
```

## Application

**Process:** Check the executor list of any Quality Gate. If 'Agent A' generates the text and 'Agent A' evaluates the rubric, you have a structural flaw. At minimum it must be 'Agent A' -> 'Clone B' -> Human. 

## Decision Tree

```
IF (Node generates an artifact independently) 
THEN NEXT NODE = QUALITY GATE (Executed by an entirely different cognitive identity).
```

## Failure Modes

### Blind Spot Endorsement
- **Trigger:** Using the same Agent thread to produce a 10-page report and asking it: "Is this report good?"
- **Manifestation:** Hallucinations are mathematically endorsed and codified as truth into the final deliverable.

## Validation

**Validation Criteria:**
- Generator executor ≠ Validator executor (REQUIRED)
- Validator is distinct cognitive identity (Clone, Human, or different Agent type) (REQUIRED)
- Quality Gate explicitly documents validator chain (REQUIRED)
- Self-validation pattern detected → VETO (BLOCKING)

**Anti-Pattern Detection:**
- Same agent generating + validating in same thread = FAIL
- Lack of intermediary validator = FAIL
- Rationale endorsement without external review = FAIL

**Success Pattern:**
- Agent A generates → Clone B validates → Human approves (or: Agent A → Agent B → Human)
