# Task: Evaluate Tool Compatibility with Squad

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools-evaluate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: discover-tools-evaluate
name: "Evaluate Tool Compatibility with Squad"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: >
  Scores and ranks classified tools using weighted criteria (official source,
  documentation, maintenance, community, capability match). Filters below
  threshold. Corresponds to Phase 1, Step 1.3 of the original pipeline.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::discover_tools_evaluate
Output: artifact::discover_tools_evaluate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Apply structured scoring to each classified tool to determine fitness for
the target squad. Filter out tools below the quality threshold. Produce a
ranked shortlist of qualified candidates.

## Prerequisites

- [ ] `discover-tools-classify` completed successfully
- [ ] Classified tools available at `.aiox/squad-runtime/discovery/{domain}/classified-tools.yaml`

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `classified_tools` | list | Yes | Output from `discover-tools-classify` |
| `prioritized_gaps` | list | Yes | From `discover-tools-scan` output |
| `budget_tier` | enum | No | Passed through from pipeline |

## Workflow

### Step 1: Score Each Tool

Apply weighted scoring criteria to every classified tool:

```yaml
mcp_scoring:
  criteria:
    official_source:
      weight: 0.30
      check: "Is from modelcontextprotocol or anthropic?"

    documentation:
      weight: 0.20
      check: "Has complete README with install + usage?"

    maintenance:
      weight: 0.20
      check: "Updated in last 6 months?"

    community:
      weight: 0.15
      check: "Stars > 50? Active issues being addressed?"

    capability_match:
      weight: 0.15
      check: "Solves a prioritized gap with full or partial match?"

  threshold: 6.0
  max_recommendations: 5
```

### Step 2: Filter Below Threshold

Remove tools scoring below 6.0. Document why each filtered tool was excluded.

### Step 3: Validate Compatibility Evidence

For each qualified tool, verify:

```yaml
compatibility_check:
  - has_install_instructions: true
  - runs_on_target_platform: true
  - no_conflicting_dependencies: true
  - compatible_with_claude_code: true
```

Tools with no compatibility evidence trigger VETO-TOOLS-002.

### Step 4: Rank Qualified Tools

Sort qualified tools by score descending. Group by the gap each tool fills.

## Output

```yaml
evaluate_output:
  tools_evaluated: N
  tools_qualified: N
  tools_filtered: N
  qualified_tools:
    - name: ""
      score: 0.0
      fills_gap: ""
      source_url: ""
      install_command: ""
      scoring_breakdown:
        official_source: 0.0
        documentation: 0.0
        maintenance: 0.0
        community: 0.0
        capability_match: 0.0
  filtered_tools:
    - name: ""
      score: 0.0
      reason: ""
```

Output file: `.aiox/squad-runtime/discovery/{domain}/evaluated-tools.yaml`

## Acceptance Criteria

- [ ] Every classified tool scored against all 5 criteria
- [ ] Threshold filtering applied (score >= 6.0)
- [ ] Each recommendation has complete scoring breakdown
- [ ] Compatibility evidence validated for all qualified tools
- [ ] Maximum 5 recommendations per execution

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-EVAL-001"
    condition: "Recommended tool has no compatibility evidence"
    trigger: "During compatibility validation (Step 3)"
    block_behavior: "BLOCK from final list until compatibility validated"
```

## Related Documents

- `discover-tools.md` -- Orchestrator (parent task)
- `discover-tools-classify.md` -- Previous task in pipeline
- `discover-tools-recommend.md` -- Next task in pipeline
- `data/quality-dimensions-framework.md` -- Quality scoring framework

---

_Task Version: 1.0.0_
_Extracted from: discover-tools.md v3.0 (Phase 1, Step 1.3)_
