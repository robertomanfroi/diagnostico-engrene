---
id: "PV_PA_008"
title: "Boundary Rigidity (Compositional Hierarchy)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Architecture"
  - "SINKRA Hierarchy"
  - "Diagnostics"
pipeline_instances:
  - "system-mapping"
  - "process-troubleshooting"
sys_tension:
  tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — Contextual exemption from hierarchy when human trust and speed are higher value than formal taxonomy"
  resolution: "Apply hierarchy discipline ONLY to inter-system or multi-executor handoffs; permit intra-human steps to flow without Atom-level documentation (Map strictly what connects distinct systems or executors)"
---

# PV_PA_008 - Boundary Rigidity (Compositional Hierarchy)

**Type:** Decision Heuristic
**Phase:** 1 (Discovery & Diagnosis)
**Agent:** @hybridOps:process-architect
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Enforce the absolute obedience to the compositional taxonomy: Token -> Atom -> Molecule -> Organism -> Template -> Instance. Prevent subjective arguments over the "process failing" globally when the fault lies in a specific micro-handoff (Molecule) or a blank assignment (Atom).

## Configuration

```yaml
PV_PA_008:
  name: "Boundary Rigidity"
  phase: 1
  pattern_reference: "HO-PP-003"

  weights:
    root_cause_depth: 1.0
    layer_obedience: 0.9

  thresholds:
    diagnostic_approval: 0.9

  veto_conditions:
    - condition: "diagnosing_organism_without_atom_check = true"
      action: "VETO - Descend the hierarchy. A macro structure does not break; its cells do."

  output:
    type: "decision"
    values: ["APPROVE_DIAGNOSIS", "DRILL_DOWN", "VETO"]
```

## Application

**Input:** Complaints ("The pipeline is broken"), Process Maps, Meeting Transcripts
**Process:** Forbid global software/process changes until the granular layer (Atom/Molecule) failure point is proven.
**Output:** APPROVE_DIAGNOSIS | DRILL_DOWN | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (a team blames the macro Workflow/Organism for continuous friction)
    THEN DRILL_DOWN to the Molecule level (Identify the broken Handoff)

SECONDARY BRANCH:
  IF (the Molecule failure is tracked down to an unexecuted Task)
    THEN DRILL_DOWN to the Atom level (Where is the ExecutorType assigned?)

TERMINATION: Macro problems are solved exclusively with Micro interventions.
CONSTRAINT: NEVER approve "scrapping the old system and moving to Asana" because of an unassigned Atom.
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Level Definition | 1.0 | ≥1.0 | Are we speaking about the right layer (Atom vs Organism)? |
| Handoff Integrity | 0.9 | ≥0.8 | Did the Molecule pass data correctly between Atoms? |
| Layer Obedience | 1.0 | =1.0 | Are we trying to skip layers to mask incompetence? |

## Confidence Requirements

- **High commitment decisions:** Demands surgical precision before declaring a systemic failure. 100% trace to the source Layer.
- **Tactical decisions:** Immediate micro-fixes on Atoms allowed, as long as mapping acknowledges the change.

## Performance Metrics

```yaml
performance:
  decision_speed: "Minutes (kills pointless meetings instantly)"
  accuracy_rate: "100% trace to truth"
  confidence_level: "99% (Inviolable Root)"
  resource_efficiency: 9/10 (Prevents massive platform migrations)
```

## Failure Modes

### Macro-Escapism (The Coward)
- **Trigger:** Meetings where everyone points at the "Pipeline" abstractly.
- **Manifestation:** Countless hours spent discussing strategy instead of fixing the fact that Designer A is receiving incomplete briefings from Copier B.
- **Detection:** Use of vague jargon ("The flow", "The system", "Alignment").
- **Recovery:** "Which Atom broke? Show me the Handoff Molecule."
- **Prevention:** Enforce extreme ownership over individual inputs.

### Granular Bureaucracy (The Zealot)
- **Trigger:** Forcing massive taxonomies onto extremely simple, high-trust human processes.
- **Manifestation:** Documenting "Token states" for tasks that take humans seconds to infer.
- **Recovery:** Map strictly what connects systems or distinct executors; let intra-human minor steps flow.

## Behavioral Evidence

**Example:** Blaming the Agile Board
- **Context:** An agency squad was repeatedly missing delivery dates.
- **Information Available:** Leadership debated whether Kanban or Scrum was the better Organism framework.
- **Heuristic Application:** Bypassed the macro debate. Drilled down to the Atom: the task "Render Final Video" was missing the Pre-Condition "Assets Uploaded". The Molecule connecting the Editor and Publisher was broken.
- **Outcome:** The framework issue vanished once the granular handoff constraint was formalized.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 1:

```yaml
checkpoint:
  id: "hierarchy-check"
  heuristic: PV_PA_008
  phase: 1

  criteria:
    - metric: "atom_level_checked"
      required: true
    - metric: "molecule_handoffs_validated"
      required: true

  veto_conditions:
    - condition: "atom_level_checked == false"
      action: "HALT - Refusal to trace failure implies abstract excuse-making"

  validation_questions:
    - "Can you point directly to the Task (Atom) where reality deviated from the map?"

  pass_action: "Approve Diagnosis"
  fail_action: "Descend Compositional Layer"
```

---

## Validation

✓ **Paradox Identified & Resolved:** Absolute hierarchy obedience (Macro-Escapism prevention) vs. Contextual flexibility (Granular Bureaucracy avoidance).
✓ **Resolution Applied:** Hierarchy discipline restricted to inter-system/multi-executor boundaries; intra-human workflows exempt from Atom-level documentation.
✓ **sys_tension Field:** Added to YAML frontmatter with tension statement and resolution strategy.
✓ **Behavioral Integrity:** The heuristic maintains surgical precision without unnecessary taxonomic overhead.

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part II
