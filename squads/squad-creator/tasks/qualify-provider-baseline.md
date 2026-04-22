# Task: Execute Opus Baseline for Cross-Provider Qualification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qualify-provider-baseline` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: qualify-provider-baseline
name: "Execute Opus Baseline for Cross-Provider Qualification"
category: qualification
agent: squad-chief
elicit: false
autonomous: true
description: >
  Runs the target task in Opus to establish a quality baseline for comparison.
  Captures output, token counts, latency, and cost. Corresponds to Phase 1
  of wf-cross-provider-qualification.yaml.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qualify_provider_baseline
Output: artifact::qualify_provider_baseline
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Produce a ground-truth Opus execution so the candidate model's output can be
measured against a known-good result. Without a valid baseline, no comparison
is possible.

## Prerequisites

- [ ] `qualify-provider-preflight` completed successfully
- [ ] `task_prompt` available from preflight output
- [ ] `test_input` resolved from cross_provider_candidates

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `task_name` | string | Yes | From preflight |
| `candidate_model` | string | Yes | From preflight (used for output path) |
| `task_prompt` | string | Yes | From preflight |
| `test_input` | object | Yes | From cross_provider_candidates |

## Workflow

### Step 1: Execute in Opus

```yaml
execution:
  subagent_type: "general-purpose"
  model: "opus"
  prompt: |
    Read squads/squad-creator/tasks/{task_name}.md completely.
    Execute the task with input: {test_input.target}
    Save output as YAML to test-cases/cross-provider/{task_name}/{candidate_model}/opus-baseline.yaml
    Include metadata: tokens used, duration_ms.
```

### Step 2: Validate baseline output

Verify the output file is non-empty and contains valid YAML.

**Veto if:** output empty or error (CPQ_VC_002).

## Output

```yaml
baseline_output:
  opus_result_file: "test-cases/cross-provider/{task_name}/{candidate_model}/opus-baseline.yaml"
  opus_tokens:
    input: 0
    output: 0
  opus_latency_ms: 0
  opus_cost_usd: 0
```

## Veto Conditions

```yaml
veto_conditions:
  - id: CPQ_VC_002
    trigger: "Opus baseline fails or output empty"
    action: "BLOCK - No baseline to compare against"
```

## Acceptance Criteria

- [ ] Opus executed the task with the configured test_input
- [ ] Output saved as YAML with metadata (tokens, duration)
- [ ] Baseline file validated as non-empty and well-formed
- [ ] Token counts and latency recorded

## Related Documents

- `wf-cross-provider-qualification.yaml` -- Parent workflow
- `qualify-provider-preflight.md` -- Previous task in pipeline

---

_Task Version: 1.0.0_
_Extracted from: wf-cross-provider-qualification.yaml v1.0 (Phase 1)_
