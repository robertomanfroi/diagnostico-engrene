---
id: "PV_PA_026"
title: "The 5-Gate Executor Decision Tree"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Core Frameworks"
  - "Execution Assignment"
pipeline_instances:
  - "executor-assignment"
sys_tension:
  tension_with: "Speed vs. Safety — Gut feeling prioritizes fast assignment but 5-Gate rigor prioritizes consequence-aware executor selection"
  resolution: "The 5-Gate Decision Tree is the constitutional override: mathematical rigor always precedes gut feeling in executor assignment"
---

# PV_PA_026 - The 5-Gate Executor Decision Tree

**Type:** Decision Heuristic
**Phase:** 3 (Assignment)
**Agent:** @hybridOps:process-architect

## Purpose

Always decide executors using the 5 cognitive gates in strict order. Gut feelings regarding AI implementation consistently fail to account for edge cases and cost scaling.

## Configuration

```yaml
PV_PA_026:
  name: "5-Gate Executor Decision Tree"
  phase: 3

  veto_conditions:
    - condition: "executor_assigned_without_running_decision_tree == true"
      action: "VETO - Force the decision through the mathematical model."
```

## Application

**Process:**
1. Deterministic task? -> **Worker**
2. Requires AI semantic API? -> **Agent**
3. High consequence/legal liability? -> **Human**
4. Strictly constrained by business methodology? -> **Clone**
5. Creative judgment at high scale? -> **Agent + Human Validator Combo**

## Decision Tree

```
IF (Gut feeling says "Use AI here") 
THEN RUN THROUGH 5-GATES TO VERIFY.
```

## Failure Modes

### Shiny Object Syndrome
- **Trigger:** A C-level executive buying an enterprise AI suite to "handle all HR" without running the consequence gate (Gate 3), leading to automated, illegal firing notifications.

---

## Validation

**Paradox Identified:** Speed of assignment vs. Safety of executor choice. Organizational instinct favors rapid actor selection (Agent for AI tasks), but legal liability and edge cases demand systematic 5-Gate validation before assignment.

**Resolution Applied:** Gate 3 (Consequence) acts as constitutional veto. Any executor assignment bypassing this gate is immediately escalated to human governance.

**Test Cases:**
- [ ] Gate 1 determinism verified before assigning Worker
- [ ] Gate 3 consequence assessment completed before AI/Agent selection
- [ ] Veto condition triggers when assignment attempts to skip systematic model
- [ ] Clone assignments explicitly require methodology containment (Gate 4) validation
