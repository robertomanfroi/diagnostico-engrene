# Task: Quality Comparison for Cross-Provider Qualification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qualify-provider-compare` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: qualify-provider-compare
name: "Quality Comparison for Cross-Provider Qualification"
category: qualification
agent: squad-chief
elicit: false
autonomous: true
description: >
  Selects the best reliability run and compares it against the Opus baseline
  across 5 weighted dimensions (completeness, accuracy, reasoning, format,
  actionability). Calculates cost savings. Corresponds to Phase 3 of
  wf-cross-provider-qualification.yaml.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qualify_provider_compare
Output: artifact::qualify_provider_compare
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Produce a structured, evidence-based quality comparison between the candidate
model's best output and the Opus baseline. This is the core decision input
for the qualification verdict.

## Prerequisites

- [ ] `qualify-provider-reliability` completed with verdict PASS or BATCH_ONLY
- [ ] Opus baseline file available
- [ ] At least one successful candidate run file available

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `task_name` | string | Yes | From pipeline |
| `candidate_model` | string | Yes | From pipeline |
| `runs` | array | Yes | From reliability output |
| `opus_baseline_file` | string | Yes | From baseline output |
| `opus_tokens` | object | Yes | From baseline output |
| `model_cost` | object | Yes | From external_models registry |
| `success_rate` | number | Yes | From reliability output |
| `threshold` | number | No | Default: 0.85 |

## Workflow

### Step 1: Select best run

Select the successful run with:
1. Lowest latency (if all similar quality)
2. Most complete output (section count)

**Output:** `best_run_file`

### Step 2: Compare across 5 dimensions

```yaml
quality_dimensions:
  completeness:
    weight: 0.30
    check: "Section count candidate vs opus"
  accuracy:
    weight: 0.30
    check: "Key decisions match (PASS/FAIL, scores)"
    veto_check: "Opposite decision triggers CPQ_VC_004"
  reasoning:
    weight: 0.20
    check: "Evidence depth and specificity"
  format:
    weight: 0.10
    check: "YAML valid, structure matches"
  actionability:
    weight: 0.10
    check: "Recommendations count and quality"
```

### Step 3: Calculate cost savings

```yaml
cost_calculation:
  opus_cost: "(opus_tokens.input * 5.00 / 1_000_000) + (opus_tokens.output * 25.00 / 1_000_000)"
  candidate_cost: "(candidate_tokens.input * model_cost.input / 1_000_000) + (candidate_tokens.output * model_cost.output / 1_000_000)"
  effective_candidate_cost: "candidate_cost / success_rate"
  savings_pct: "(1 - effective_candidate_cost / opus_cost) * 100"
```

## Output

```yaml
compare_output:
  best_run_file: ""
  dimension_scores:
    completeness: 0.0
    accuracy: 0.0
    reasoning: 0.0
    format: 0.0
    actionability: 0.0
  quality_score: 0.0
  gaps: []
  opus_cost_usd: 0.0
  candidate_cost_usd: 0.0
  effective_cost_usd: 0.0
  savings_percentage: 0.0
  saved_to: "test-cases/cross-provider/{task_name}/{candidate_model}/quality-comparison.yaml"
```

## Veto Conditions

```yaml
veto_conditions:
  - id: CPQ_VC_004
    trigger: "Opposite decision from Opus (PASS vs FAIL)"
    action: "BLOCK - Model not qualified (wrong decision)"
```

## Acceptance Criteria

- [ ] Best run selected from successful runs
- [ ] All 5 dimensions scored with weights applied
- [ ] Overall quality score calculated as weighted average
- [ ] Cost savings calculated with reliability adjustment
- [ ] Gaps documented explicitly
- [ ] Quality comparison file saved

## Related Documents

- `wf-cross-provider-qualification.yaml` -- Parent workflow
- `qualify-provider-reliability.md` -- Previous task in pipeline
- `qualify-provider-ptbr.md` -- Next task in pipeline (conditional)

---

_Task Version: 1.0.0_
_Extracted from: wf-cross-provider-qualification.yaml v1.0 (Phase 3)_
