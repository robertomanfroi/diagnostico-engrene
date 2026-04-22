---
id: "PV_PA_032"
title: "Template Parametrization"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Scaling"
  - "Organism Layer"
pipeline_instances:
  - "process-architecture"
sys_tension:
  tension_with: "Customization Demand"
  description: "Increasing parametrization for reusability creates template complexity that demands customization for edge cases, contradicting the original goal of reducing custom builds."
  resolution: "Establish parametrization ceiling: define maximum conditional branches per template. Once exceeded, spawn a new template variant or return to custom engineering."
---

# PV_PA_032 - Template Parametrization

**Type:** Decision Heuristic
**Phase:** 5 (Optimization)
**Agent:** @hybridOps:process-architect

## Purpose

A Process Template is an Organism parameterized for infinite reusability. If you find yourself building a "new process" from scratch (e.g. a content pipeline) every time the client or platform format changes slightly, you are destroying scalability. Build the core Organism once; Parametrize the variables via Template.

## Configuration

```yaml
PV_PA_032:
  name: "Template Parametrization"
  phase: 5

  veto_conditions:
    - condition: "reengineering_entire_organism_for_each_new_client == true"
      action: "VETO - Transform the core Organism into a parameterized Template."
```

## Application

**Process:** Filter operational request pipelines. Are they identical flows simply requiring a slightly different target variable? (e.g. "YouTube Workflow" vs "TikTok Workflow"). Consolidate immediately.

## Decision Tree

```
IF (Process repeats structurally with minor contextual variable shifts) 
THEN PACKAGE AS TEMPLATE (Do not allow manual redraws).
```

## Failure Modes

### Custom Build Exhaustion
- **Trigger:** Rebuilding the entire creative content wave logic block by block for five different niche clients, wasting weeks of architectural time instead of deploying instantiated templates.

## Validation

✓ **Paradox Identified:** Parametrization (efficiency goal) vs Customization Demand (outcome).
✓ **Resolution Defined:** Parametrization ceiling enforces template bounded complexity.
✓ **Applicability:** Scales to any process replication scenario where template variants exceed 3-4 conditional branches.
