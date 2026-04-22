<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-from-sop-load-classify
  task_name: Create From SOP -- Load + Classify
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Environment + Source Package
  - Source Classification
  acceptance_criteria:
  - Loader executed with explicit business and selectors
  - All 4 environment gates passed
  - Every loaded YAML classified into exactly one class
  - No source outside `workspace/businesses/{slug}` considered valid
  - Environment validated
  output_persistence: canonical_workspace
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Create From SOP -- Load + Classify

**Task ID:** create-from-sop-load-classify
**Parent Task:** `create-from-sop.md`
**Purpose:** Run deterministic loader, validate environment gates, classify sources into 3 classes
**Execution Type:** Hybrid (Worker script + Agent classification)
**Model:** `Opus`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Create From SOP -- Load + Classify |
| **status** | `active` |
| **responsible_executor** | @pedro-valerio |
| **execution_type** | Hybrid |
| **input** | `--business={slug}` + `--namespace` and/or `--paths` |
| **output** | Classified sources YAML |
| **action_items** | 2 steps |
| **acceptance_criteria** | Environment validated, all sources classified |

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CFS-001 | Business slug must be explicit | `--business=<slug>` present | VETO - BLOCK |
| VETO-CFS-002 | Must resolve to `full_workspace_mode` | Loader output check | VETO - BLOCK |
| VETO-CFS-003 | Source of truth must be `workspace_canonical` | Loader output check | VETO - BLOCK |
| VETO-CFS-004 | At least one SOP selector required | `--namespace` or `--paths` present | VETO - BLOCK |
| VETO-CFS-005 | All selectors must resolve | `missing_requested_sources == []` | VETO - BLOCK |

---

## Workflow

### Step 0: Environment + Source Package

```bash
node squads/squad-creator-pro/scripts/load-business-sops.cjs \
  --business={slug} \
  --namespace={namespace} \
  --paths={paths} \
  --format=yaml
```

Confirm:

- `coo_readiness_status == ready`
- `runtime_mode == full_workspace_mode`
- `source_of_truth == workspace_canonical`
- `missing_requested_sources == []`

If any gate fails: STOP.

### Step 1: Source Classification

For each loaded YAML, classify into one of these classes:

- `executable_process` -> describes process, routine, operation, scorecard, structure or flow that becomes task/workflow
- `supporting_context` -> business context, positioning, offer, narrative, constraint
- `governance_signal` -> ownership, status, score, version, evidence, sources

**Rules:**

- `L1-strategy/*.yaml` tends to be `executable_process`
- `L3-product/*/offerbook.yaml` tends to be `supporting_context`
- metadata, evidence, sources never become tasks directly; they become guardrails

**Critical rule:** `namespace` and `paths` are source selectors, not output instructions.

---

## Output Contract

```yaml
source_classification:
  business_slug: "{slug}"
  environment:
    coo_readiness_status: "ready"
    runtime_mode: "full_workspace_mode"
    source_of_truth: "workspace_canonical"
  selectors:
    namespaces: []
    explicit_paths: []
  sources:
    executable_process:
      - path: "{path}"
        description: "{what process it describes}"
    supporting_context:
      - path: "{path}"
        description: "{what context it provides}"
    governance_signal:
      - path: "{path}"
        description: "{what governance data it contains}"
  missing_requested_sources: []
```

---

## Completion Criteria

- [ ] Loader executed with explicit business and selectors
- [ ] All 4 environment gates passed
- [ ] Every loaded YAML classified into exactly one class
- [ ] No source outside `workspace/businesses/{slug}` considered valid

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `create-from-sop-map-workflow.md` |
| **Trigger** | Classification complete |
| **Artifact** | `source_classification` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of create-from-sop.md_

## Acceptance Criteria

- [ ] Environment validated
- [ ] all sources classified
