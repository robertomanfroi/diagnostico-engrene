---
id: "PV_PA_031"
title: "Organism Sequencing (Temporal Dimension)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Sinkra Hierarchy"
  - "Organism Layer"
pipeline_instances:
  - "process-architecture"
sys_tension:
  tension_with: "Molecules must remain structurally timeless AND Organisms add temporal constraints that limit Molecule reusability"
  resolution: "Molecules define valid patterns; Organisms orchestrate their sequence. A Molecule with hard-coded temporal limits is a veto. Temporal constraints belong exclusively to Organism layer, enabling Molecule portability across different time/SLA contexts."
---

# PV_PA_031 - Organism Sequencing

**Type:** Decision Heuristic
**Phase:** 4 (Organism Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

An Organism (Pipeline, Wave, State Machine) is strictly where **TIME** and **CHRONOLOGY** enter the equation. It orders timeless structural Molecules into a distinct path (Beginning, Middle, End). Never strictly enforce chronological constraints at the lower molecular layer.

## Configuration

```yaml
PV_PA_031:
  name: "Organism Sequencing"
  phase: 4

  veto_conditions:
    - condition: "molecule_hard_codes_chronological_time_limits_between_unrelated_tasks == true"
      action: "VETO - Molecule is structural; Organism dictates the chronology."
```

## Application

**Process:** Verify the process diagrams. High-level flows establishing timelines (SLA for delivery, dependencies, chronological start triggers) belong strictly at the Organism level.

## Decision Tree

```
IF (Component maps out strict chronological progression of states)
THEN LEVEL = ORGANISM.
```

## Failure Modes

### Temporal Confusion
- **Trigger:** Forcing a Handoff Molecule to include a rigid "30-day" cooling-off period locally, effectively blocking anyone from ever using that Handoff pattern for rapid daily transactions.

---

## Validation

✅ **Paradox identified:** Molecules must be reusable (timeless) yet Organisms introduce temporal constraints that restrict Molecule portability.

✅ **Resolution applied:** Temporal constraints (SLA, sequencing, dependencies) exclusively belong to Organism layer. Molecules remain structurally agnostic to time, enabling reuse across different execution contexts.

✅ **Veto condition validated:** Hard-coded chronological limits in Molecule definitions MUST trigger a VETO. Time flows at Organism level only.
