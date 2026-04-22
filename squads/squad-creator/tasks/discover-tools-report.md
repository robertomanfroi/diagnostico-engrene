# Task: Generate Discovery Report with Action Items

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools-report` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: discover-tools-report
name: "Generate Discovery Report with Action Items"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: >
  Generates the final Tool Discovery Report, Capability Map, and Integration
  Plan files from consolidated recommendations. Corresponds to Phase 2,
  Step 2.4 of the original pipeline.
accountability:
  human: squad-operator
  scope: review_only

```


<!-- SINKRA_CONTRACT -->
Domain: `{domain}`
atomic_layer: Atom
Input: request::discover_tools_report
Output: artifact::discover_tools_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Produce the three deliverable artifacts of the discover-tools pipeline:
the human-readable discovery report, the machine-readable capability map,
and the actionable integration plan.

## Prerequisites

- [ ] `discover-tools-recommend` completed successfully
- [ ] Recommendations at `.aiox/squad-runtime/discovery/{domain}/recommendations.yaml`
- [ ] Scan results at `.aiox/squad-runtime/discovery/{domain}/scan-results.yaml`

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `recommend_output` | object | Yes | Output from `discover-tools-recommend` |
| `scan_output` | object | Yes | Output from `discover-tools-scan` |
| `domain` | string | Yes | Passed through from pipeline |

## Workflow

### Step 1: Generate Tool Discovery Report

Write to `.aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md`:

```markdown
# Tool Discovery Report: {Squad Name}

**Generated:** {date}
**Domain:** {domain}
**Gaps Analyzed:** {N}
**MCP Servers Discovered:** {total}

## Executive Summary
{1-paragraph summary of findings}

## Capability Gaps Identified
| Capability | Priority | MCPs Found | Recommended |
|------------|----------|------------|-------------|

## MCP Server Recommendations

### Quick Wins (Implement Now)
| MCP Server | Fills Gap | Score | Effort | Install Command |
|------------|-----------|-------|--------|-----------------|

### Strategic (Plan for)
{...}

## Impact vs Effort Matrix
{quadrant analysis}

## Integration Plan

### Immediate (Today)
- [ ] {action}

### Short-term (This Week)
- [ ] {action}

## Pro Version Available
For comprehensive discovery covering APIs, CLIs, Libraries, GitHub Projects,
and Skills/Prompts, install squad-creator-pro and run *discover-tools.

## Next Steps
1. {next step}
2. {next step}
```

### Step 2: Generate Capability Map

Write to `.aiox/squad-runtime/discovery/{domain}/capability-tools.yaml`:

```yaml
capability_map:
  domain: "{domain}"
  generated: "{date}"
  mappings:
    - capability: ""
      covered_by:
        internal: []
        external: []
      status: "covered|partial|gap"
```

### Step 3: Generate Integration Plan

Write to `.aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md`:

Structured markdown with immediate, short-term, and evaluate-later sections,
each with concrete steps, effort estimates, and dependencies.

### Step 4: Validate Report Completeness (SC_TDR_001)

```yaml
checkpoint: SC_TDR_001
name: "Tool Discovery Report Complete"
blocking: true
criteria:
  - all_gaps_researched: true
  - at_least_1_tool_per_gap: true
  - impact_effort_scored: true
  - integration_plan_created: true
  - report_generated: true
```

## Output

| Output | Location |
|--------|----------|
| Tool Discovery Report | `.aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md` |
| Capability Map | `.aiox/squad-runtime/discovery/{domain}/capability-tools.yaml` |
| Integration Plan | `.aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md` |

## Acceptance Criteria

- [ ] Report contains executive summary, gap table, recommendations, and integration plan
- [ ] Capability map is machine-readable YAML
- [ ] Integration plan has actionable steps with effort estimates
- [ ] SC_TDR_001 checkpoint passes all 5 criteria
- [ ] Pro upgrade note included in report

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-REPORT-001"
    condition: "Recommendations output is empty or missing"
    trigger: "Before report generation"
    block_behavior: "BLOCK report; nothing to report"
```

## Related Documents

- `discover-tools.md` -- Orchestrator (parent task)
- `discover-tools-recommend.md` -- Previous task in pipeline

---

_Task Version: 1.0.0_
_Extracted from: discover-tools.md v3.0 (Phase 2, Step 2.4 + Outputs)_
