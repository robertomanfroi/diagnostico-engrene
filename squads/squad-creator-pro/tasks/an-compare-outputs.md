---
task-id: an-compare-outputs
name: "Compare Model Outputs"
version: 3.0.0
execution_type: Orchestrator
model: Opus
model_rationale: "Orchestrator stub -- delegates to 1 consolidated sub-task. Opus REQUIRED (evaluator independence)."
haiku_eligible: false
note: "v3.0.0: De-atomized from 3 subtasks to 1. load was pure data marshaling, report was a post-condition of score."
estimated-time: 15-20 min
complexity: medium

inputs:
  required:
    - task_name: "Task being evaluated (e.g., an-assess-sources)"
    - opus_baseline: "Path to Opus output file"
    - haiku_output: "Path to Haiku output file"
    - task_file: "Original task definition (for reference)"

outputs:
  primary:
    - qualification_report: "Full qualification report with decision"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-compare-outputs
  task_name: Compare Model Outputs
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 15-20m
  domain: Operational
  input:
  - '{''task_name'': ''Task being evaluated (e.g., an-assess-sources)''}'
  - '{''opus_baseline'': ''Path to Opus output file''}'
  - '{''haiku_output'': ''Path to Haiku output file''}'
  - '{''task_file'': ''Original task definition (for reference)''}'
  output:
  - '{''qualification_report'': ''Full qualification report with decision''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Both output files loaded and parsed
  - All 4 dimensions scored using rubric
  - Veto conditions checked
  - Total score calculated
  - Decision determined (QUALIFIED/CONDITIONAL/NOT_QUALIFIED)
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Compare Model Outputs

**Command:** `*compare-outputs`

> **CRITICAL:** Evaluator Independence -- Opus ONLY. NEVER use Haiku to evaluate Haiku.

---

## Pipeline (1 Consolidated Task)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `an-compare-outputs-score` | Load, Score & Report | 15-20 min |

> **v3.0.0 Change:** De-atomized from 3 subtasks. `load` was pure data marshaling and `report` was a post-condition of `score`. All merged into a single task with 3 sequential steps.

---

## Execution Flow

```
an-compare-outputs-score
  Step 1: Load & Extract (parse YAML, validate, normalize)
  Step 2: Score 4 Dimensions (tier_match, score_variance, checkpoint_match, recommendation_quality)
  Step 3: Determine Verdict & Report (thresholds, rationale, save)
  |
  v
[QUALIFIED | CONDITIONAL | NOT_QUALIFIED]
```

---

## Evaluator Rules

```yaml
evaluator_rules:
  model: "opus"
  blind_mode: false
  bias_mitigation:
    - "Score WHAT IS WRITTEN, not what you expect"
    - "Do NOT assume Opus is better - measure objectively"
    - "If outputs are equivalent, say so"
```

---

## Qualification Thresholds

| Decision | Criteria |
|----------|---------|
| QUALIFIED | >= 85 points AND no veto triggered |
| CONDITIONAL | 70-84 points OR veto with mitigation possible |
| NOT_QUALIFIED | < 70 points OR hard veto |

---

## Output

Save to: `squads/squad-creator-pro/test-cases/{task_name}/qualification-report.yaml`

---

## Completion Criteria

- [ ] Both output files loaded and parsed
- [ ] All 4 dimensions scored using rubric
- [ ] Veto conditions checked
- [ ] Total score calculated
- [ ] Decision determined (QUALIFIED/CONDITIONAL/NOT_QUALIFIED)
- [ ] Report saved to test-cases/{task}/qualification-report.yaml

## Task Anatomy

- **Executor:** Agent
- **Inputs:** task_name; opus_baseline; haiku_output; task_file
- **Outputs:** Full qualification report with decision
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions in subtask

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Full qualification report with decision
- [ ] Task output validated against quality standards
