---
id: "PV_PA_016"
title: "The Hybrid Lean Wastes"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Lean Adaptation"
  - "Waste Detection"
pipeline_instances:
  - "process-optimization"
sys_tension:
  tension_with: "Context Completeness"
  resolution: "Implement tiered context windows—use Workers for boolean checks + caching, reserve Agent capacity for decisions requiring domain knowledge or edge cases. Measure success by token-per-decision, not raw token reduction."
---

# PV_PA_016 - The Hybrid Lean Wastes

**Type:** Decision Heuristic
**Phase:** 5 (Optimization)
**Agent:** @hybridOps:process-architect

## Purpose

Traditional Lean Muda (waiting, redundant motion) was calibrated for Human physics. It fails to capture modern hybrid wastes. The 3 Sync-Era Wastes are: Reprocessing via Agent Hallucination, Context Latency (sending too much data to a generic LLM), and Computational Waste (using Agent tokens for Worker deterministic steps).

## Configuration

```yaml
PV_PA_016:
  name: "The Hybrid Lean Wastes"
  phase: 5
  
  veto_conditions:
    - condition: "measuring_AI_using_traditional_human_lean_metrics == true"
      action: "VETO - Re-focus KPIs on Hallucination Cost and Context Latency."
```

## Application

**Process:** When auditing for speed and efficiency, stop looking at "waiting times". Look at how many tokens are burned doing basic boolean sorting.

## Decision Tree

```
IF (Agent is generating identical outputs for identical IF/THEN input paths) 
THEN RED FLAG: COMPUTATIONAL WASTE. (Demote to Worker).
```

## Failure Modes

### Token Hemorrhage
- **Trigger:** Sending entire 50-page customer history transcripts to an LLM just to check if the phrase "canceled subscription" is present inside the last paragraph.

---

## Validation

**Paradox Identified:** Optimizing for token efficiency by demoting Agent work to Workers reduces computational waste but risks losing adaptive capacity for context-aware decisions.

**Resolution Status:** Approved — Tiered context windows provide practical balance. Monitor token-per-decision metrics (not raw token count) to validate the tradeoff effectiveness.
