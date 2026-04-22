---
id: "PV_PA_003"
title: "Agent Reasoning Gap (Not a Fast Human)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Agent Profile"
  - "AI Integration"
pipeline_instances:
  - "task-allocation"
  - "cognitive-routing"
sys_tension:
  tension_with: "PV_KE_049 (O Agnosticismo do Atributo) — Agent Interchangeability in Theory vs. Accountability Boundaries in Practice"
  resolution: "Hybrid routing: Agent handles information processing (triage, summarization, draft generation); Human handles emotional engagement, judgment, and accountability. Neither pure speed nor pure caution; structured division of labor."
---

# PV_PA_003 - Agent Reasoning Gap (Not a Fast Human)

**Type:** Decision Heuristic
**Phase:** 3 (Executor Selection)
**Agent:** @hybridOps:executor-designer
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Enforce the absolute boundary between an Agent (Language Logic) and a Human (Empathetic/Legal Judgment). Prevents the catastrophic misallocation of Agents to tasks requiring emotional nuance, relationship negotiation, or high-stakes accountability.

## Configuration

```yaml
PV_PA_003:
  name: "Agent Reasoning Gap"
  phase: 3
  pattern_reference: "HO-PP-003"

  weights:
    emotional_subtext_required: 0.9
    legal_accountability_required: 0.9

  thresholds:
    agent_eligibility_score: 0.8

  veto_conditions:
    - condition: "legal_accountability_required = true"
      action: "VETO - Route to Human Executor"
    - condition: "emotional_subtext_required = true"
      action: "VETO - Route to Human Executor"

  output:
    type: "decision"
    values: ["ROUTE_TO_AGENT", "ROUTE_TO_HUMAN", "VETO"]
```

## Application

**Input:** Task definitions, SLA requirements, Customer journey maps
**Process:** Evaluate if the speed of an Agent compromises the human relationship or legal safety.
**Output:** ROUTE_TO_AGENT | ROUTE_TO_HUMAN | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (task involves legal signatures, financial irreversibility, or moral accountability)
    THEN ROUTE_TO_HUMAN

SECONDARY BRANCH:
  ELSE IF (task requires sensing user hesitation, negotiation, or emotional pacification)
    THEN ROUTE_TO_HUMAN

TERTIARY BRANCH:
  ELSE IF (task requires semantic reasoning, abstract synthesis, or large data extraction)
    THEN ROUTE_TO_AGENT

TERMINATION: Agent handles cognition and generation; Human handles consequence and emotion.
CONSTRAINT: NEVER use an Agent to fast-track relationship-critical interactions.
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Relational Weight | 0.9 | <0.4 | Does it break trust if handled by a machine? |
| Accountability | 0.9 | =0.0 | Is someone legally/financially responsible? |
| Analytical Load | 0.8 | >0.7 | Does the task exhaust a human brain rapidly? |

## Confidence Requirements

- **High commitment decisions:** Absolute 100% confidence requirement that no legal/moral lines are crossed before assigning an Agent to client-facing closure paths.
- **Tactical decisions:** internal document generation can default to Agent with 60% confidence.

## Performance Metrics

```yaml
performance:
  decision_speed: "Immediate routing"
  accuracy_rate: "99% (prevents catastrophic AI brand damage)"
  confidence_level: "95% (ensures humans remain the bottleneck for empathy)"
  resource_efficiency: 8/10
```

## Failure Modes

### Efficiency Trap (The Coward)
- **Trigger:** Replacing humans with Agents just because SLA response time drops from 40min to 12sec.
- **Manifestation:** "Resolution Rate" looks great, but NPS and actual lifetime value collapse.
- **Detection:** Customer friction increases post-interaction despite fast metric tracking.
- **Recovery:** Reposition the Agent to draft the response internally, forcing a Human to approve/send.
- **Prevention:** Do not tie operational success strictly to speed metrics.

### Innovation Paralysis (The Zealot)
- **Trigger:** Banning all agents from customer-facing environments due to one bad auto-reply.
- **Manifestation:** Burnout of the human team doing pure semantic triage.
- **Recovery:** Divide process: Agent summarizes/tags input → Human replies.

## Behavioral Evidence

**Example:** Quick Classification vs True Support
- **Context:** An agency wants lightning-fast responses via WhatsApp using LLMs.
- **Information Available:** The LLM responds perfectly but loses clients who just needed relationship management.
- **Heuristic Application:** Re-routed the task: Agent classifies the pain point and drafts a summary, Human engages emotionally.
- **Outcome:** Kept processing speed high while preserving the human handshake, maximizing conversions.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 3:

```yaml
checkpoint:
  id: "agent-boundary-check"
  heuristic: PV_PA_003
  phase: 3

  criteria:
    - metric: "relational_risk_score"
      threshold: 0.5
      operator: "<"
    - metric: "accountability_requirement"
      required: false

  veto_conditions:
    - condition: "accountability_requirement == true"
      action: "HALT - AI cannot assume legal/moral accountability"

  validation_questions:
    - "Is there implied subtext or emotional friction in this task?"
    - "Can the business afford a probabilistic hallucination here?"

  pass_action: "Assign Agent Executor"
  fail_action: "Assign Human Executor"
```

---

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part I

## Validation

✓ **Paradox Identified:** Speed (Agent efficiency) vs. Trust (Human accountability)
✓ **Resolution Applied:** Hybrid execution model splits cognitive load from relational responsibility
✓ **Tension Encoded:** sys_tension field captures the dynamic equilibrium between automation and empathy
✓ **Operational Clarity:** Heuristic prevents false dichotomy by establishing criteria for when each executor type adds value
