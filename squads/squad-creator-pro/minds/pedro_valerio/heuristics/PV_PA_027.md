---
id: "PV_PA_027"
title: "Hierarchical Independence (No Level Skips)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Sinkra Hierarchy"
  - "Structural Integrity"
pipeline_instances:
  - "process-mapping"
sys_tension:
  tension_with: "Operational Velocity (PV_PA_026)"
  resolution: "Balance strict hierarchy enforcement with pragmatic fast-path exceptions for critical incidents; document each skip and retroactively formalize the intermediate levels post-crisis"
---

# PV_PA_027 - Hierarchical Independence

**Type:** Decision Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

The Sinkra 6-Level Hierarchy commands that a level is composed strictly of the level immediately beneath it (e.g., An Organism is made of Molecules, a Molecule of Atoms). Bypassing levels entirely destroys predictability, reusability, and auditability.

## Configuration

```yaml
PV_PA_027:
  name: "Hierarchical Independence"
  phase: 4

  veto_conditions:
    - condition: "organism_composed_directly_of_tokens_bypassing_atoms == true"
      action: "VETO - Do not skip levels. Formalize the Atoms and Molecules."
```

## Application

**Process:** Ensure pipeline steps are built sequentially. You cannot have a high-level "Wave" directly interacting with a low-level "Status Token" without going through a Task Atom first. 

## Decision Tree

```
IF (Diagram skips from Pipeline Organism down to Priority tag) 
THEN REJECT AND RE-MAP THE INTERMEDIATE MOLECULES.
```

## Failure Modes

### Spaghetti Architecture
- **Trigger:** Slapping 'P0' on a massive month-long Wave without atomizing the tasks inside it. The team is paralyzed because 'everything is P0' at the macro level.

---

## Validation

**Paradox Identified:** Strict enforcement of hierarchical levels creates gridlock during operational emergencies, where speed supersedes structure. Resolution requires a dual-mode system: normal mode (enforce hierarchy) and crisis mode (allow controlled skips with post-incident formalization).

**Validation Checklist:**
- [ ] All Organisms reference only Molecules, never Atoms/Tokens
- [ ] All Molecules reference only Atoms, never Tokens
- [ ] Level skips (if any) are explicitly documented in exception log with justification
- [ ] Post-incident retroactive formalization tasks created before crisis mode expires
- [ ] Hierarchy violations trigger automated alerts in process-mapping pipeline
