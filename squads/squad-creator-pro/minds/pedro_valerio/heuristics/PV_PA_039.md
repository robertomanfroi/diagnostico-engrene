---
id: "PV_PA_039"
title: "Probabilistic Gateway (The Gray Zone)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Process Modeling"
  - "Decision Nodes"
pipeline_instances:
  - "handoff-design"
sys_tension:
  tension_with: "BPMN Binary Logic vs. Agent Probabilistic Output"
  resolution: "Three-path gateway (Accept threshold >0.8 | Reject threshold <0.3 | Gray Zone escalation 0.3-0.8) preserves process rigor while honoring agent uncertainty"
---

# PV_PA_039 - Probabilistic Gateway

**Type:** Decision Heuristic
**Phase:** 3 (Decision Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

BPMN rigidly forces binary Yes/No representation at gateways. In Hybrid operations, any gateway operated by an Agent is Probabilistic (e.g. 0.0 to 1.0 confidence). You must always architect a "Gray Zone" branch to safely eject borderline cases out of the AI pipeline and into Human review.

## Configuration

```yaml
PV_PA_039:
  name: "Probabilistic Gateway"
  phase: 3

  veto_conditions:
    - condition: "agent_gateway_forces_absolute_binary_pathing == true"
      action: "VETO - Agent outputs are stochastic. Build a Gray margin."
```

## Application

**Process:** Never write purely `if > 0.5 then YES`. Use `if > 0.8 YES, if < 0.3 NO, else GREY_ZONE -> HUMAN_REVIEW`. Validate the threshold bounds. 

## Decision Tree

```
IF (Decision Node executor == Agent) 
THEN ENFORCE THREE-PATH OUTCOME (Accept | Reject | Escalate to Human).
```

## Failure Modes

### False Binary Extinction
- **Trigger:** Auto-rejecting a prime recruitment candidate directly because the Semantic Matching Agent scored it a 69% on rigid keywords instead of the binary baseline of 70%, dumping valuable outliers.

## Validation

✓ **Paradox Recognized:** Binary pathway architecture conflicts with probabilistic agent outputs — resolved via three-path escalation model
✓ **Threshold Rationale:** 0.8+ (high confidence accept) | <0.3 (high confidence reject) | 0.3-0.8 gray zone preserves outlier quality
✓ **Human Escalation:** Gray zone cases bypass rigid logic, preventing false extinctions of high-value candidates
