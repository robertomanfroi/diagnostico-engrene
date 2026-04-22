<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-clone-review-stages-fidelity
  task_name: Clone Review -- Stages + Fidelity
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
  - Stage Architecture Review (Binary Checkpoints)
  - Quick Fidelity Check (Binary Checkpoints)
  acceptance_criteria:
  - Stage architecture reviewed with binary checkpoints
  - Needs-stages assessment completed if no stages present
  - Quick fidelity scored with 5 checkpoints
  - Fidelity estimate classification assigned
  - All checkpoints scored binary
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Clone Review -- Stages + Fidelity

**Task ID:** an-clone-review-stages-fidelity
**Parent Task:** `an-clone-review.md`
**Purpose:** Review stage architecture and perform quick fidelity check with binary checkpoints
**Execution Type:** Hybrid (Worker script 90% + Agent interpretation 10%)
**Model:** `Haiku`
**Haiku Eligible:** YES

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Clone Review -- Stages + Fidelity |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | Clone file path + preflight YAML |
| **output** | Stage architecture score + Quick fidelity score |
| **action_items** | 2 steps |
| **acceptance_criteria** | All checkpoints scored binary, needs-stages assessed |

---

## Workflow

### Step 1: Stage Architecture Review (Binary Checkpoints)

**First check if clone uses stages:**

```yaml
has_stages: grep -c "stages:" file.md > 0
```

**IF has stages (5 checkpoints):**

| # | Checkpoint | Passes if... |
|---|------------|-------------|
| 1 | Stages defined | `stages:` section exists |
| 2 | 2+ stages | At least 2 stages defined |
| 3 | Each stage has trigger | Each stage has `trigger:` or `when:` |
| 4 | Each stage has behavior | Each stage has `behavior:` or `response:` |
| 5 | Transitions defined | Exists `transition:` or flow between stages |

**IF no stages, check if NEEDS them:**

| # | Check | Result |
|---|-------|--------|
| 1 | Prompt > 500 lines? | If yes -> probably needs |
| 2 | Multiple contexts? | If yes -> probably needs |
| 3 | Behavior varies? | If yes -> probably needs |

### Step 2: Quick Fidelity Check (Binary Checkpoints)

**5 quick checkpoints (not full fidelity score):**

| # | Checkpoint | What to look for | Passes if... |
|---|------------|------------------|-------------|
| 1 | Voice DNA exists | `voice_dna:` section | Section exists |
| 2 | Has signature phrases | `signature_phrases:` | 3+ phrases |
| 3 | Thinking DNA exists | `thinking_dna:` section | Section exists |
| 4 | Has frameworks | `frameworks:` or `mental_models:` | 2+ frameworks |
| 5 | Has immune system | `veto:` or `never:` or `objection:` | Protection section exists |

**Quick Fidelity Score = count(passed) / 5 x 100**

---

## Output Contract

```yaml
stages_fidelity_scores:
  stages:
    has_stages: true|false
    needs_stages: true|false
    stage_score: {0-5}
    gaps: []
  quick_fidelity:
    checkpoints_passed: []
    checkpoints_failed: []
    score: {0-5}
    percentage: "{%}"
    estimate: "Incomplete|Basic|Intermediate|Premium|Elite"
```

---

## Completion Criteria

- [ ] Stage architecture reviewed with binary checkpoints
- [ ] Needs-stages assessment completed if no stages present
- [ ] Quick fidelity scored with 5 checkpoints
- [ ] Fidelity estimate classification assigned

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `an-clone-review-report.md` |
| **Trigger** | Stages + fidelity scores complete |
| **Artifact** | `stages_fidelity_scores` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-clone-review.md_

## Acceptance Criteria

- [ ] All checkpoints scored binary
- [ ] needs-stages assessed
