---
id: "PV_PA_025"
title: "The Intent vs Process Distinction"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Axioms"
  - "Governance"
pipeline_instances:
  - "process-mining"
sys_tension:
  - tension_with: "Adaptive Execution (PV_PA_XXX)"
    resolution: "Define 'Executor Type' as role+fallback hierarchy, not singular assignment. Allow substitution only within declared constraints."
---

# PV_PA_025 - The Intent vs Process Distinction

**Type:** Decision Heuristic
**Phase:** 1 (Discovery)
**Agent:** @hybridOps:process-architect

## Purpose

If a mapped step lacks a formally defined Executor Type (leaving it to "whoever is available"), it is not a "Process"—it is merely a folklore "Intent." Intents produce wildly inconsistent outputs because execution mechanics shift randomly based on employee capacity.

## Configuration

```yaml
PV_PA_025:
  name: "Intent vs Process Distinction"
  phase: 1

  veto_conditions:
    - condition: "task.executor_type == null OR task.executor == 'Any Available Player'"
      action: "VETO - This is an intent. Define the actual Executor Type."
```

## Application

**Process:** Audit existing organizational charts or Notion boards. If a card says "Review Briefing" but nobody knows if the Director, PM, or GPT-4 is supposed to do it today, the process is fundamentally broken. 

## Decision Tree

```
IF (Executor is unassigned or relies on 'cultural osmosis') 
THEN REJECT PIPELINE (Failure is structurally guaranteed).
```

## Failure Modes

### Shifting Accountability
- **Trigger:** A stage marked 'Upload Assets' fails constantly because the editor thought the designer did it, and the designer waited for a Worker script that was never built.

## Validation

✓ **Paradox Identified:** Rigidity vs. Adaptability — Process clarity demands fixed executors, but organizational reality requires flexibility.

✓ **Resolution Mechanism:** Implement executor hierarchies (primary → secondary → fallback) with explicit substitution rules, rather than leaving execution to chance.

✓ **Testability:** Audit processes to confirm: (a) Executor type is documented, (b) Fallback chain exists, (c) Failures trace to capability gaps, not role confusion.
