<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-clone-review-report
  task_name: Clone Review -- Report
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
  - Calculate Overall Verdict
  - Generate Report
  acceptance_criteria:
  - Overall verdict calculated from trinity + fidelity scores
  - All sections populated with data from prior sub-tasks
  - Priority actions listed with target component and impact
  - Next version path defined with concrete percentage targets
  - Report has all sections
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


# Task: Clone Review -- Report

**Task ID:** an-clone-review-report
**Parent Task:** `an-clone-review.md`
**Purpose:** Generate consolidated review report with verdicts, gaps, and priority actions
**Execution Type:** Hybrid (Worker script 90% + Agent interpretation 10%)
**Model:** `Haiku`
**Haiku Eligible:** YES

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Clone Review -- Report |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | `source_trinity_scores` + `stages_fidelity_scores` from prior sub-tasks |
| **output** | Complete `clone_review` YAML report |
| **action_items** | 2 steps |
| **acceptance_criteria** | Report has all sections, verdicts calculated, priority actions listed |

---

## Workflow

### Step 1: Calculate Overall Verdict

```python
trinity_percentage = source_trinity_scores.trinity.percentage
fidelity_estimate = stages_fidelity_scores.quick_fidelity.percentage

if trinity_percentage >= 80 and fidelity_estimate >= 80:
    verdict = "SOLID"
elif trinity_percentage >= 60 and fidelity_estimate >= 60:
    verdict = "NEEDS_WORK"
else:
    verdict = "REBUILD"
```

### Step 2: Generate Report

```yaml
clone_review:
  clone: "{name}"
  clone_file: "{path}"
  date: "{date}"

  source_quality:
    total_sources: {n}
    ouro_count: {n}
    bronze_count: {n}
    ouro_percentage: "{%}"
    curadoria_score: "excelente|aceitavel|critico"
    sources_checked:
      - file: "{name}"
        tier: "ouro|bronze"
        checkpoints_passed: [1,2,3,4,5]

  trinity:
    playbook:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    framework:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    swipe_file:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    total_score: {0-15}
    max_score: 15
    percentage: "{%}"
    verdict: "SOLID|NEEDS_WORK|REBUILD"

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
    estimate: "Intermediate (V2.0)"

  overall:
    trinity_percentage: "{%}"
    fidelity_estimate: "{%}"
    verdict: "SOLID|NEEDS_WORK|REBUILD"

  priority_actions:
    - action: "{what to do first}"
      target_component: "playbook|framework|swipe|stages|fidelity"
      checkpoints_to_fix: [3,5]
      impact: "alto|medio"

  next_version_path: "From {current}% to {target}% closing {n} gaps"
```

---

## Completion Criteria

- [ ] Overall verdict calculated from trinity + fidelity scores
- [ ] All sections populated with data from prior sub-tasks
- [ ] Priority actions listed with target component and impact
- [ ] Next version path defined with concrete percentage targets

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-clone-review.md_

## Acceptance Criteria

- [ ] Report has all sections
- [ ] verdicts calculated
- [ ] priority actions listed
