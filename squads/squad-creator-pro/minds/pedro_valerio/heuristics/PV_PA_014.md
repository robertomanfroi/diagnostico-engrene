---
id: "PV_PA_014"
title: "The BPMN Swimlane Veto (Generic AI Lane Trap)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Modeling"
  - "Visual Clarity"
pipeline_instances:
  - "process-mapping"
sys_tension:
  tension_with: "Generic 'AI Lane' grouping masks stochastic/deterministic operational differences"
  resolution: "Explicit swimlane taxonomy: @Agent (stochastic), @Worker (deterministic), @Clone (heuristic) — each with distinct KPIs and error budgets"
---

# PV_PA_014 - The BPMN Swimlane Veto

**Type:** Decision Heuristic
**Phase:** 1 (Discovery)
**Agent:** @hybridOps:process-architect

## Purpose

Never place all automation into a single generic "AI" BPMN swimlane or category. Grouping an Agent (stochastic), Worker (deterministic), and Clone (heuristic) into the same visual bucket masks critical operational differences, error rates, and costs.

## Configuration

```yaml
PV_PA_014:
  name: "BPMN Swimlane Veto"
  phase: 1

  veto_conditions:
    - condition: "diagram_contains_generic_AI_swimlane == true"
      action: "VETO - Separate into distinct Agent, Worker, and Clone lanes."
```

## Application

**Process:** Look at your process flowchart. Do you have a lane just called "Automation" or "AI"? 
**Output:** SHRED IT. Split it immediately to reveal the truth of the system.

## Decision Tree

```
IF (Documentation lumps an LLM and a Python scraper into the same swimlane)
THEN REJECT AND RE-DRAW.
```

## Failure Modes

### The Homogeneous Box Trap
- **Trigger:** Consulting firms drawing a single magic "AI System" box on the chart.
- **Manifestation:** Managers try to enforce deterministic KPIs on a stochastic LLM because it's in the same "swimlane" as the database trigger.

## Validation

**Paradox Resolved:** The heuristic prevents generic "AI lane" grouping by mandating explicit taxonomy separation.
- ✓ BPMN diagram distinguishes @Agent lanes from @Worker lanes from @Clone lanes
- ✓ Each swimlane has declared SLA/error-rate expectations matching execution model
- ✓ Documentation explicitly lists stochastic vs deterministic boundaries
- ✓ Process review checklist includes swimlane taxonomy verification step

**Tension:** Avoid recreating the generic "AI" trap when explaining the heuristic itself — always reference specific executor types by role.
