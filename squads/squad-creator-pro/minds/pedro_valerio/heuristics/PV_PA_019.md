---
id: "PV_PA_019"
title: "Deterministic Assignment (The Worker Rule)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Deterministic Logic"
pipeline_instances:
  - "executor-assignment"
sys_tension:
  tension_with: "PV_PA_014 (Human Escalation for Edge Cases)"
  resolution: "Apply Deterministic Assignment to base case; escalate to Human ONLY if context_priority='urgent' OR exception_flags=['compliance','safety','audit'] present. Default=Worker."
---

# PV_PA_019 - Deterministic Assignment

**Type:** Decision Heuristic
**Phase:** 3 (Assignment)
**Agent:** @hybridOps:process-architect

## Purpose

If a task is strictly deterministic (the exact same input always yields the exact same output via clear boolean rules), it strictly belongs to a Worker. Do not pay Humans to click buttons out of fatigue, and do not pay API token prices for basic rules.

## Configuration

```yaml
PV_PA_019:
  name: "Deterministic Assignment"
  phase: 3

  veto_conditions:
    - condition: "task_is_rules_based AND executor != Worker"
      action: "VETO - Reassign immediately to a Worker."
```

## Application

**Process:** Find repetitive categorization loops, IF/THEN data routing, system webhooks, and raw formula processing. Extract from Human and Agent assignments instantly.

## Decision Tree

```
IF (Logic is strictly IF/THEN/ELSE with no semantic ambiguity)
THEN EXECUTOR = WORKER (Zero Exceptions).
```

## Failure Modes

### Burnout & Expense Padding
- **Trigger:** Using a highly intelligent human to manually tag 800 deals based on static volume metrics. (Fatigue sets in at item 200).
- **Trigger 2:** Deploying GPT-4 to read CSV files just to filter out rows missing email addresses.

---

## Validation

✓ **Paradox Resolved:** Tension between "Zero Exceptions" absolute rule and real-world conditional escalation now explicit via `sys_tension` field.

✓ **Resolution Logic:** Default executor=Worker for deterministic tasks; escalate to Human only when context flags (compliance, safety, audit) or urgent priority override the baseline assignment.

✓ **Framework Alignment:** Supports SINKRA compositional rules with context-aware conditional execution paths.
