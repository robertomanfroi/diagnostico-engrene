---
id: "PV_PA_007"
title: "Synthetic Waste (Miscalibrated Metrics)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Analytics"
  - "Lean Adaptation"
  - "Performance Tracking"
pipeline_instances:
  - "process-audit"
  - "kpi-definition"
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Fallback Rate Tracking"
  resolution: "Measure accuracy (fallback rate, token cost) alongside speed; reject pure SLA metrics for AI executors"
---

# PV_PA_007 - Synthetic Waste (Miscalibrated Metrics)

**Type:** Decision Heuristic
**Phase:** 5 (Optimization & Analytics)
**Agent:** @hybridOps:process-architect
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Prevent the catastrophic illusion of operational success by banning human-centric metrics (like Wait Time, Motion) on synthetic executors. Forces tracking to shift towards the true metrics of algorithmic processes: Toxicity of Input, Fallback Rate, and Token Cost.

## Configuration

```yaml
PV_PA_007:
  name: "Synthetic Waste"
  phase: 5
  pattern_reference: "HO-PP-003"

  weights:
    fallback_rate_tracking: 1.0
    input_toxicity_monitoring: 0.9

  thresholds:
    acceptable_fallback_rate: 0.15

  veto_conditions:
    - condition: "primary_kpi == 'lead_time' AND executor_type IN ['Worker', 'Agent']"
      action: "VETO - Algorithmic execution creates zero wait. Track accuracy/fallback."

  output:
    type: "decision"
    values: ["APPROVE_METRICS", "RECALIBRATE_KPIS", "VETO"]
```

## Application

**Input:** Dashboards, Process OKRs, Lean/Six-Sigma reports.
**Process:** Strip out "time-based" and "motion-based" metrics for machine-execution steps, replacing them with AI-centric success metrics.
**Output:** APPROVE_METRICS | RECALIBRATE_KPIS | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (the executor is a Worker or Agent AND the KPI implies human physical/mental exhaustion limits)
    THEN RECALIBRATE_KPIS (Focus on semantic success, JSON validity, Fallback frequency)

SECONDARY BRANCH:
  ELSE IF (the KPI is pure execution speed)
    THEN evaluate against the cost of the token footprint. Is speed burning budget?

TERMINATION: Machines don't tire; they hallucinate and throw exceptions. Measure the exceptions.
CONSTRAINT: NEVER applaud a process solely for operating instantly if its output requires downstream human scrubbing.
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Fallback Rate | 1.0 | <15% | How often does the AI hand the task back to a human? |
| Input Quality | 0.9 | ≥0.9 | Is the JSON schema intact on 90% of requests? |
| SLA Obsession | 0.8 | =0.0 | Discontinue SLA celebration for API calls. |

## Confidence Requirements

- **High commitment decisions:** Data ingestion layers must strictly measure format breakage before accepting AI "success" stories.
- **Tactical decisions:** Use rough tracking for internal bot operations where human triage is inherently present.

## Performance Metrics

```yaml
performance:
  decision_speed: "Continuous monitoring"
  accuracy_rate: "95% metric alignment"
  confidence_level: "100% (eliminates the 'Green Dashboard Illusion')"
  resource_efficiency: 10/10
```

## Failure Modes

### The Green Dashboard Illusion (The Coward)
- **Trigger:** Checking off "AI Implementation Success" because a bot reduced ticket wait time to 3 seconds.
- **Manifestation:** Managers celebrate; customers churn secretly because the bot's instant answer was fundamentally useless.
- **Detection:** Re-open rate of tickets climbs; identical queries repeat.
- **Recovery:** Swap the KPI. Did the bot *resolve* the intent, or did it just *close* the loop?
- **Prevention:** Always track Customer Engagements Post-Bot.

### Analytic Paralysis (The Zealot)
- **Trigger:** Attempting to build 50 new metrics just because "we have AI now".
- **Manifestation:** Dashboard bloat distracts the team from core business health.
- **Recovery:** Consolidate to top 3 metrics: Fallback Rate, API Cost, TTR (Time to True Resolution).

## Behavioral Evidence

**Example:** Support Bot Triage Metrics
- **Context:** An e-commerce bot fired instant answers to shipping inquiries.
- **Information Available:** Board reported 100% SLA compliance for Q2.
- **Heuristic Application:** Audited the 'Fallback Rate'—65% of the instant answers led to frustrated customers clicking "Talk to Human" anyway.
- **Outcome:** Ripped out 'Speed to First Response' from the main dashboard, replaced it with 'First-Touch True Resolution', radically changing prompt optimization goals.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 5:

```yaml
checkpoint:
  id: "kpi-calibration-check"
  heuristic: PV_PA_007
  phase: 5

  criteria:
    - metric: "has_fallback_tracking"
      required: true
    - metric: "primary_kpi_is_sla"
      expected_value: false

  veto_conditions:
    - condition: "primary_kpi_is_sla == true AND executor_is_ai == true"
      action: "HALT - AI speed is irrelevant if accuracy is toxic"

  validation_questions:
    - "Are we measuring the machine as if it were a tired human?"
    - "Do we know how often the automation silently fails?"

  pass_action: "Approve Analytics Stack"
  fail_action: "Return to KPI Definition"
```

---

## Validation

✅ **Paradox Identified:** Speed (instant bot response) vs. Accuracy (65% fallback rate). The Green Dashboard Illusion masks true failure.

✅ **Systemic Tension:** Velocity Obsession (celebrate SLA compliance) ⟷ AI Reality (speed ≠ resolution). Resolution requires measuring fallback and token cost.

✅ **Application Verified:** HO-PP-003 Quality Gate checkpoint includes fallback tracking as mandatory criterion.

✅ **Real-World Evidence:** Support bot case study confirms 100% SLA ≠ customer satisfaction when true resolution rate is low.

---

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part I
