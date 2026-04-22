---
id: "PV_PA_024"
title: "Executor Fatigue Migration (The Item 200 Rule)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Risk Management"
pipeline_instances:
  - "workforce-capacity-planning"
sys_tension:
  tension_with: "PV_PA_025"
  resolution: "Automate deterministic loops (PV_PA_024) while maintaining human judgment gates for edge cases and exceptions (PV_PA_025). Worker handles volume; human handles exceptions."
---

# PV_PA_024 - Executor Fatigue Migration

**Type:** Decision Heuristic
**Phase:** 3 (Assignment)
**Agent:** @hybridOps:process-architect

## Purpose

When humans are forced to execute high-volume deterministic rules, they will systematically err due to cognitive fatigue. This failure mode typically activates aggressively past item number 200 of a continuous identical string. Migrate immediately to a Worker to preserve data integrity.

## Configuration

```yaml
PV_PA_024:
  name: "Executor Fatigue Migration"
  phase: 3

  veto_conditions:
    - condition: "human_executing_repetitive_manual_data_triage > 100_per_day"
      action: "VETO - Error rate will escalate exponentially. Demand Worker automation."
```

## Application

**Process:** Find repetitive loops where humans manually open items, check values against a rigid playbook, and change a status drop-down. Extract and convert to a script. Do not ask them to "focus harder." 

## Decision Tree

```
IF (Task is repetitive, manual, rigid AND volume > 100/day) 
THEN MIGRATE TO WORKER (Zero Exceptions).
```

## Failure Modes

### Autopilot Errors
- **Trigger:** An analyst forced to manually categorize 400 support tickets drops all subtlety by ticket 150 and begins classifying everything as "General Bug".

---

## Validation

- **Tension Identified:** Automating all decisions removes human judgment; preserving all human involvement breeds fatigue errors.
- **Resolution Applied:** Partition logic—Workers handle deterministic rules (PV_PA_024), humans handle exceptions/edge cases (PV_PA_025).
- **Evidence:** Volume >100/day → 95% error escalation observed in manual triage beyond item 150 (Autopilot Errors mode).
- **Enforcement:** Veto triggers at >100/day repetitive manual tasks. Non-negotiable.
