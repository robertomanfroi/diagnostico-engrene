# Task: Pre-Flight Validation for Cross-Provider Qualification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qualify-provider-preflight` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: qualify-provider-preflight
name: "Pre-Flight Validation for Cross-Provider Qualification"
category: qualification
agent: squad-chief
elicit: false
autonomous: true
description: >
  Validates inputs, checks model availability via LLM Router, reads the target
  task file, and creates the test directory. Corresponds to Phase 0 of
  wf-cross-provider-qualification.yaml.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qualify_provider_preflight
Output: artifact::qualify_provider_preflight
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Ensure all preconditions are met before running a cross-provider qualification:
the task must exist in the candidates registry, the candidate model must be
allowed for that task, and the model must respond to a health ping.

## Prerequisites

- [ ] squad-chief agent is active
- [ ] `wf-cross-provider-qualification.yaml` loaded with `cross_provider_candidates`
- [ ] LLM Router service available at `services/llm-router/`

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `task_name` | string | Yes | Task name (without .md) |
| `candidate_model` | enum | Yes | External model key (e.g. glm5, kimi) |
| `cross_provider_candidates` | object | Yes | Registry from workflow |

## Workflow

### Step 1: Check cross_provider_candidates

Lookup `task_name` in `cross_provider_candidates`.

**Veto if:** task_name not in registry (CPQ_VC_001).

### Step 2: Check model in test_with list

Verify `candidate_model` is in the task's `test_with` array.

**Veto if:** model not allowed for this task.

### Step 3: Check model availability

```bash
node services/llm-router/bin/check-model.js {candidate_model}
```

Verify model responds to ping.

**Veto if:** model unavailable or API error.

### Step 4: Read task file

Read `squads/squad-creator/tasks/{task_name}.md` completely.

**Output:** `task_prompt` -- full task content.

### Step 5: Create test directory

```bash
mkdir -p squads/squad-creator/test-cases/cross-provider/{task_name}/{candidate_model}/
```

## Output

```yaml
preflight_output:
  task_name: ""
  candidate_model: ""
  task_prompt: ""
  test_input: {}
  test_directory: ""
  model_available: true
```

## Veto Conditions

```yaml
veto_conditions:
  - id: CPQ_VC_001
    trigger: "Task not in cross_provider_candidates"
    action: "BLOCK - Add input to registry first"
  - id: CPQ_VC_PREFLIGHT_MODEL
    trigger: "Model not in task's test_with list"
    action: "BLOCK - Model not allowed for this task"
  - id: CPQ_VC_PREFLIGHT_AVAIL
    trigger: "Model API unavailable"
    action: "BLOCK - Model not responding"
```

## Acceptance Criteria

- [ ] Task validated against cross_provider_candidates registry
- [ ] Model validated against task's test_with list
- [ ] Model health check passed
- [ ] Task file read and content captured
- [ ] Test directory created

## Related Documents

- `wf-cross-provider-qualification.yaml` -- Parent workflow
- `qualify-task.md` -- Internal tier qualification (different scope)

---

_Task Version: 1.0.0_
_Extracted from: wf-cross-provider-qualification.yaml v1.0 (Phase 0)_
