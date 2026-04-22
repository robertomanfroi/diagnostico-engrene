---
id: "PV_PA_029"
title: "Atom Functionality Limit (Singularity)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Sinkra Hierarchy"
  - "Atom Layer"
pipeline_instances:
  - "task-structuring"
sys_tension:
  tension_with: "PV_PA_030 (Molecule Composition through Sequencing)"
  resolution: "Atoms enforce no-internal-sequencing; Molecules wrap Atoms + temporal orchestration. The paradox resolves via layering: atomicity is a property of the grain, composition happens at the next layer up."
---

# PV_PA_029 - Atom Functionality Limit

**Type:** Decision Heuristic
**Phase:** 2 (Atom Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

Atoms (Tasks, Fields, Triggers, Actions, Constraints) are the smallest functional combinations. They must execute a single clear objective without temporal sequencing. If you are inserting multi-step chronologies inside an Atom, you are designing a Molecule.

## Configuration

```yaml
PV_PA_029:
  name: "Atom Functionality Limit"
  phase: 2

  veto_conditions:
    - condition: "atom_contains_chronological_multi_step_sequence == true"
      action: "VETO - Break it down into discrete Atoms and assemble a Molecule."
```

## Application

**Process:** Look at Task descriptions. If the instructions say "Do X, wait for response, then do Y, and if Y is good, upload Z", that is NOT a Task. That is a Pipeline. Break it apart.

## Decision Tree

```
IF (Task definition includes distinct temporal pauses or nested logic flows) 
THEN SPLIT INTO MULTIPLES.
```

## Failure Modes

### Bloated Tasks
- **Trigger:** Writing a Prompt for an Agent that instructs it to act as Researcher, Writer, Editor, and Publisher simultaneously, generating total logical failure and context dropout.

---

## Validation

✓ **Paradox identified:** Atoms must have zero internal sequencing, yet Molecules (higher layer) ARE sequences of Atoms.

✓ **Resolution:** The singularity principle applies only within the Atom boundary. Sequencing belongs to the Molecule layer, which orchestrates atomic units without violating their internal constraints.

✓ **Application verified:** When decomposing a Process, if you find yourself writing "do X, then wait, then do Y", you have not identified a single Atom—you have identified a Molecule that requires atomic decomposition first, followed by explicit sequencing rules in the Molecule configuration.
