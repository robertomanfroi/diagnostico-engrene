# Task: Generate Cross-Provider Qualification Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qualify-provider-report` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: qualify-provider-report
name: "Generate Cross-Provider Qualification Report"
category: qualification
agent: squad-chief
elicit: false
autonomous: true
description: >
  Aggregates all evidence from previous phases into a structured qualification
  report. Optionally updates model-routing.yaml for qualified models. Displays
  a summary banner. Corresponds to Phase 5 of wf-cross-provider-qualification.yaml.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qualify_provider_report
Output: artifact::qualify_provider_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Produce the final, consolidated qualification report that captures every
measurement and verdict. Update the routing configuration when a model
qualifies. This is the single source of truth for the qualification decision.

## Prerequisites

- [ ] `qualify-provider-compare` completed
- [ ] `qualify-provider-ptbr` completed (or skipped with reason)
- [ ] All evidence files present in test directory

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `task_name` | string | Yes | From pipeline |
| `candidate_model` | string | Yes | From pipeline |
| `baseline_output` | object | Yes | From qualify-provider-baseline |
| `reliability_output` | object | Yes | From qualify-provider-reliability |
| `compare_output` | object | Yes | From qualify-provider-compare |
| `ptbr_output` | object | Yes | From qualify-provider-ptbr |
| `model_info` | object | Yes | From external_models registry |

## Workflow

### Step 1: Generate qualification report

Create `test-cases/cross-provider/{task_name}/{candidate_model}/qualification-report.yaml`:

```yaml
report_structure:
  cross_provider_qualification_report:
    task_name: "{task_name}"
    candidate_model: "{candidate_model}"
    test_date: "{today}"
    workflow_version: "1.1"
    baseline:
      model: "opus"
      cost_usd: "{opus_cost}"
      tokens: { input: 0, output: 0 }
      latency_ms: 0
      file: "opus-baseline.yaml"
    candidate:
      model: "{candidate_model}"
      provider: "{model_info.provider}"
      reliability:
        runs: 0
        success_rate: "0%"
        avg_latency_ms: 0
        latency_range: "0-0ms"
        verdict: ""
      quality:
        overall_score: "0%"
        dimension_scores: {}
        gaps: []
      cost:
        per_run_usd: "0"
        effective_usd: "0"
        vs_opus_savings: "0%"
      pt_br:
        tested: false
        overall_score: "0/10"
        verdict: ""
    decision:
      final: "QUALIFIED|QUALIFIED_BATCH_ONLY|NOT_QUALIFIED"
      recommended_use: ""
      caveats: []
    privacy_assessment:
      risk_level: ""
      recommendation: "self-host|api|do-not-use"
    evidence_files: []
```

### Step 2: Update model-routing.yaml (conditional)

```yaml
update_condition: "decision is QUALIFIED or QUALIFIED_BATCH_ONLY"
update_target: "model-routing.yaml → external_alternatives"
update_content:
  task_name:
    external_alternative:
      model: "{candidate_model}"
      qualified: true
      quality_vs_opus: "{quality_score}%"
      savings: "{savings_pct}%"
      batch_only: true/false
      pt_br_qualified: true/false
      tested_date: "{today}"
```

### Step 3: Display summary

```
CROSS-PROVIDER QUALIFICATION RESULT
------------------------------------
Task:        {task_name}
Candidate:   {candidate_model} ({display_name})

RELIABILITY  {success_rate}% success | {avg_latency}ms avg
QUALITY      {quality_score}% vs Opus | {gaps_count} gaps
PT-BR        {ptbr_overall}/10 | {ptbr_verdict}
COST         Opus ${opus_cost} vs ${candidate_cost} | {savings_pct}% savings

DECISION:    {final_decision}
PRIVACY:     {privacy_risk} -> {privacy_recommendation}
```

## Output

```yaml
report_output:
  report_file: "test-cases/cross-provider/{task_name}/{candidate_model}/qualification-report.yaml"
  routing_updated: true/false
  final_decision: "QUALIFIED|QUALIFIED_BATCH_ONLY|NOT_QUALIFIED"
```

## Acceptance Criteria

- [ ] Qualification report generated with all sections populated
- [ ] All evidence files referenced in the report
- [ ] model-routing.yaml updated if model qualified
- [ ] Summary displayed with all key metrics
- [ ] Privacy assessment included

## Related Documents

- `wf-cross-provider-qualification.yaml` -- Parent workflow
- `qualify-provider-ptbr.md` -- Previous task in pipeline
- `config/model-routing.yaml` -- Routing configuration

---

_Task Version: 1.0.0_
_Extracted from: wf-cross-provider-qualification.yaml v1.0 (Phase 5)_
