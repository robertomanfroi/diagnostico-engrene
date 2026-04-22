---
id: "PV_PA_012"
title: "The Invisible Executor Trap"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Architecture"
  - "Execution Assignment"
pipeline_instances:
  - "process-mapping"
  - "hybrid-ops-audit"
sys_tension:
  tension_with: "PV_KE_069 (O Paradoxo do Executor-First) vs Transparência de Executor no Design"
  resolution: "Define executor type at mapping time (explicit binding), use executor abstraction layer at runtime (permits swapping). Declarative process models with pluggable executor implementations."
---

# PV_PA_012 - The Invisible Executor Trap

**Type:** Decision Heuristic
**Phase:** 1 (Discovery)
**Agent:** @hybridOps:process-architect
**Pattern:** HO-PP-012

## Purpose

A process model designed strictly for human executors breaks silently when AI or Workers are introduced. The map effectively lies about the territory. Prevent operational gaps by explicitly declaring the executor type in the process definition before scaling.

## Configuration

```yaml
PV_PA_012:
  name: "The Invisible Executor Trap"
  phase: 1

  weights:
    criticality: 1.0

  veto_conditions:
    - condition: "process_mapped_with_implicit_human_executor == true"
      action: "VETO - Redraw process to specify the 4 Sync-Era executor types."

  output:
    type: "decision"
    values: ["APPROVE", "REJECT", "RECONFIGURE"]
```

## Application

**Input:** Any process diagram or workflow mapping (e.g., BPMN, Notion SOPs).
**Process:** Scan the steps. If the executor type is missing under the assumption that "a person does it", but the infrastructure uses triggers, bots, or AI, halt operations.
**Output:** RECONFIGURE

## Decision Tree

```
IF (diagram simply says 'Execute' without defining Human/Agent/Worker/Clone)
THEN REJECT (The process is merely an intent, not a validated hybrid system).
```

## Behavioral Evidence

**Context:** Over-automation of legacy processes.
**Heuristic Application:** Ensure the exact nature of the operational unit doing the work is flagged so expectations of fidelity and error modes are accurate.

## Failure Modes

### Illusion of Automation
- **Trigger:** Adding an Agent to a legacy procedure workflow smoothly.
- **Manifestation:** No one updates the diagram; the Agent begins hallucinating output logic but teams think humans are still gatekeeping the step.
- **Detection:** Silent, untracked operational drop-off.

## Validation

✓ **Paradox Identified:** Explicit executor binding reduces operational flexibility; implicit flexibility masks executor risks.

✓ **Resolution Applied:** Use executor type declarations in process definitions with runtime abstraction layer enabling safe swapping without process diagram mutation.

✓ **Implementation Gate:** Process mappings MUST include `executor_type: [human|agent|worker|clone]` field. No diagrams pass validation without this declaration.

✓ **Evidence:** SINKRA composition rules enforce `executor_binding_schema` in `process-mapping-rules.yaml`. Sync-Era executor model validated per `PV_PA_012` heuristic.
