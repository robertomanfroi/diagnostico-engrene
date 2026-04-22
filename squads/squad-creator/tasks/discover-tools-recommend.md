# Task: Generate Prioritized Tool Recommendations

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools-recommend` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: discover-tools-recommend
name: "Generate Prioritized Tool Recommendations"
category: discovery
agent: squad-chief
elicit: true
autonomous: false
description: >
  Consolidates scan, classification, and evaluation outputs. Calculates
  impact-vs-effort matrix. Generates prioritized integration plan with
  quick wins, strategic investments, and items to evaluate later.
  Corresponds to Phase 2, Steps 2.1-2.3 of the original pipeline.
accountability:
  human: squad-operator
  scope: full
domain: Strategic

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::discover_tools_recommend
Output: artifact::discover_tools_recommend
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Synthesize all discovery phases into actionable recommendations. Calculate
ROI for each tool using impact-vs-effort analysis. Produce a prioritized
integration plan with clear action items and timelines.

## Prerequisites

- [ ] `discover-tools-evaluate` completed successfully
- [ ] Evaluated tools at `.aiox/squad-runtime/discovery/{domain}/evaluated-tools.yaml`
- [ ] Scan results at `.aiox/squad-runtime/discovery/{domain}/scan-results.yaml`

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `evaluated_tools` | list | Yes | Output from `discover-tools-evaluate` |
| `scan_output` | object | Yes | Output from `discover-tools-scan` |
| `domain` | string | Yes | Passed through from pipeline |

## Workflow

### Step 1: Consolidate All Findings

```yaml
consolidation:
  combine:
    - scan_output        # Internal-first baseline + local skills
    - evaluated_tools    # Scored MCP candidates

  deduplicate:
    - "Same tool found in multiple phases"

  categorize_by_gap:
    - gap: "{capability}"
      tools: []
      skills: []
```

### Step 2: Calculate Impact vs Effort Matrix

```yaml
impact_effort_matrix:
  for_each_tool:
    impact_score:
      - capability_coverage: 0-10
      - quality_improvement: 0-10
      - automation_gain: 0-10

    effort_score:
      - installation_complexity: 0-10
      - integration_time: "hours/days"
      - cost: "$0/free | $X/month | enterprise"
      - learning_curve: "low | medium | high"
      - is_skill: true/false  # Skills get near-zero effort bonus

    roi_score: impact_score / effort_score

  quadrants:
    quick_wins: "High impact, low effort"
    strategic: "High impact, high effort"
    fill_ins: "Low impact, low effort"
    avoid: "Low impact, high effort"
```

### Step 3: Generate Integration Plan

```yaml
integration_plan:
  immediate_actions:
    - tool: "{name}"
      action: "Install and configure"
      effort: "15 minutes"

  short_term:
    - tool: "{name}"
      action: "Install, configure, and test integration"
      effort: "1 hour"

  evaluate_later:
    - tool: "{name}"
      reason: "Need to verify compatibility"
```

Present the integration plan to the user for validation (elicit: true).

## Output

```yaml
recommend_output:
  recommendations:
    quick_wins: []
    strategic: []
    fill_ins: []
    avoid: []
  integration_plan:
    immediate: []
    short_term: []
    evaluate_later: []
  capability_map:
    - gap: ""
      recommended_tool: ""
      alternative: ""
```

Output file: `.aiox/squad-runtime/discovery/{domain}/recommendations.yaml`

## Acceptance Criteria

- [ ] All qualified tools scored for impact vs effort
- [ ] Quadrant classification applied (quick wins, strategic, fill-ins, avoid)
- [ ] Integration plan has concrete steps with effort estimates
- [ ] Quick wins clearly identified
- [ ] User validated recommendations (elicit gate)

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-REC-001"
    condition: "No evaluated tools available"
    trigger: "Before consolidation"
    block_behavior: "BLOCK recommendations; no tools to recommend"
```

## Related Documents

- `discover-tools.md` -- Orchestrator (parent task)
- `discover-tools-evaluate.md` -- Previous task in pipeline
- `discover-tools-report.md` -- Next task in pipeline
- `data/decision-heuristics-framework.md` -- Decision logic reference

---

_Task Version: 1.0.0_
_Extracted from: discover-tools.md v3.0 (Phase 2, Steps 2.1-2.3)_
