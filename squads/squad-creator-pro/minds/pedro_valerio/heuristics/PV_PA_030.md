---
id: "PV_PA_030"
title: "Molecular Pattern Recognition"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Sinkra Hierarchy"
  - "Molecule Layer"
pipeline_instances:
  - "process-mapping"
sys_tension:
  - tension_with: "PV_PA_001"
    resolution: "Standard Molecules provide guardrails; Atomic Discovery allows controlled variance. Use Molecules as baseline, permit Layer-1 variance only when business value justifies engineering cost and edge-case coverage is proven."
---

# PV_PA_030 - Molecular Pattern Recognition

**Type:** Decision Heuristic
**Phase:** 3 (Molecular Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

When Atoms cluster repeatedly (e.g., Task + Validator + Constraint = Quality Gate), label it as a Molecule. Recognizing structural recurrent patterns allows you to import proven processes instead of reinventing the wheel defensively every time.

## Configuration

```yaml
PV_PA_030:
  name: "Molecular Pattern Recognition"
  phase: 3

  veto_conditions:
    - condition: "reengineering_standard_quality_gate_from_scratch == true"
      action: "VETO - Import the standard Quality Gate Molecule. Do not invent."
```

## Application

**Process:** Scan flows for sequences like Approval steps, Handoffs, Escalations. Force the team to use the pre-established Sinkra Catalogs for these Molecules to ensure robust edge-case coverage right away.

## Decision Tree

```
IF (Cluster pattern is common across multiple domains) 
THEN PACKAGE AS MOLECULE (Standardize it across the ecosystem).
```

## Failure Modes

### Redundant Engineering
- **Trigger:** An operations team spending 3 weeks developing custom logic for handling feedback revisions between a Copywriter and an Editor, completely ignoring that the "Feedback Loop" Molecule solves this out of the box.

---

## Validation

✓ **Paradox Identified:** Standardization via Molecules vs. flexibility for domain-specific customization. Resolution: Use Molecules as proven baseline; permit variance only with explicit business justification and edge-case validation.

✓ **System Tension Documented:** Maps to PV_PA_001 (Atomic Discovery) — establishes the boundary between atomic variance (low-level) and molecular reuse (high-level).

✓ **Actionable:** Teams must consult Sinkra Catalog FIRST before engineering. Custom logic only after proving catalog gaps.
