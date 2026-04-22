---
id: "PV_PA_034"
title: "The 4-Question Level Diagnosis"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Mapping"
  - "Sinkra Hierarchy"
pipeline_instances:
  - "hybrid-ops-audit"
sys_tension:
  tension_with: "open-ended iterative debugging"
  resolution: "Use 4-Question framework as entry point to abstraction level; permit iterative context-switching between levels once level is established"
---

# PV_PA_034 - The 4-Question Level Diagnosis

**Type:** Decision Heuristic
**Phase:** 1 (Diagnostics)
**Agent:** @hybridOps:process-architect

## Purpose

Instantly establish the correct layer of abstraction when diagnosing a broken process to prevent teams from arguing at cross-purposes (e.g., someone complaining about a Token value while the PM attempts to fix a Wave flow). Use 4 hardcoded questions.

## Configuration

```yaml
PV_PA_034:
  name: "4-Question Level Diagnosis"
  phase: 1

  veto_conditions:
    - condition: "team_arguing_about_process_definition_without_level_agreement == true"
      action: "VETO - Halt debate. Apply the 4 Questions."
```

## Application

**Process:** 
1. Value without behavior? -> **Token**. 
2. Smallest functional task combination? -> **Atom**. 
3. Timeless structural pattern (e.g. validator check)? -> **Molecule**. 
4. Sequential chronological states? -> **Organism**.

## Decision Tree

```
IF (Debugging a broken pipeline step) 
THEN IDENTIFY HIERARCHY LEVEL FIRST before adjusting logic.
```

## Failure Modes

### Cross-Abstraction Arguing
- **Trigger:** An engineer pushing for a structural re-haul of the entire "Pipeline" (Organism) because one "Formatting step" (Atom) requires adjustment.

---

## Validation

✓ **Abstraction Clarity:** Framework properly distinguishes Token → Atom → Molecule → Organism levels
✓ **Diagnostic Determinism:** 4-question sequence is deterministic and consistently routes diagnosis to correct level
✓ **Tension Resolution:** Resolved via staged entry point (4 questions first) with permitted context-switching post-diagnosis
✓ **Failure Mode Coverage:** Cross-abstraction arguing explicitly addressed as veto condition
