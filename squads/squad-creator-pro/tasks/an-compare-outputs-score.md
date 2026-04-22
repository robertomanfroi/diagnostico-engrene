---
task-id: an-compare-outputs-score
name: "Load, Score & Report — Model Output Comparison"
version: 2.0.0
execution_type: Agent
model: Opus
model_rationale: "Opus REQUIRED for evaluator independence. NEVER use Haiku to evaluate Haiku."
haiku_eligible: false
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
    - qualification_report: "Complete report with decision, rationale, and recommendations"
    - report_path: "squads/squad-creator-pro/test-cases/{task_name}/qualification-report.yaml"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-compare-outputs-score
  task_name: Load, Score & Report — Model Output Comparison
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 15-20m
  domain: Operational
  input:
  - '{''task_name'': ''Task being evaluated (e.g., an-assess-sources)''}'
  - '{''opus_baseline'': ''Path to Opus output file''}'
  - '{''haiku_output'': ''Path to Haiku output file''}'
  - '{''task_file'': ''Original task definition (for reference)''}'
  output:
  - '{''qualification_report'': ''Complete report with decision, rationale, and recommendations''}'
  - '{''report_path'': ''squads/squad-creator-pro/test-cases/{task_name}/qualification-report.yaml''}'
  action_items:
  - Load and validate both output files
  - Extract and normalize comparable items
  - Score all 4 evaluation dimensions
  - Check veto conditions
  - Determine qualification decision
  - Write rationale and save report
  acceptance_criteria:
  - Both files loaded and parsed successfully
  - All scored items extracted and aligned
  - Structural differences noted
  - Items normalized for 1:1 comparison
  - All 4 dimensions scored per rubric
  - Calculations are reproducible and shown
  - Veto conditions checked and documented
  - Total score calculated
  - Decision determined using thresholds
  - Rationale explains the decision
  - Recommendations are actionable
  - Report saved to correct path
  - Report includes all dimension details
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


# Task: Load, Score & Report -- Model Output Comparison

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-compare-outputs-score` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `an-compare-outputs` (orchestrator)
- **Sequence:** 1 of 1 (consolidated from 3 subtasks in v1.0.0)

## Purpose

Load both model outputs, score across 4 evaluation dimensions, determine qualification decision, and produce the final report. Consolidated from `an-compare-outputs-load`, `an-compare-outputs-score`, and `an-compare-outputs-report` (v1.0.0).

---

## Step 1: Load & Extract

> Merged from `an-compare-outputs-load` v1.0.0

### 1a. Load and Validate Inputs

```yaml
validation:
  - "Both files exist and are valid YAML"
  - "Both files have same structure"
  - "Task file provides context for evaluation"
```

### 1b. Extract Comparable Items

```yaml
extract:
  items: "List of scored items (sources, dimensions, etc.)"
  scores: "Numerical scores per item"
  tiers: "Classification tiers per item"
  checkpoints: "Binary checkpoints if applicable"
  recommendations: "Action items and priorities"
```

### 1c. Normalize for Comparison

Align items from both outputs so each can be compared 1:1:
- Match items by ID or name
- Note items present in one output but not the other
- Flag structural differences

**Intermediate structure:**

```yaml
comparable_items:
  total_items: 0
  matched_items: 0
  unmatched_items: 0
  items:
    - id: ""
      opus_score: 0
      haiku_score: 0
      opus_tier: ""
      haiku_tier: ""
      opus_checkpoints: []
      haiku_checkpoints: []
  opus_recommendations: []
  haiku_recommendations: []
```

---

## Step 2: Score 4 Dimensions

> Merged from `an-compare-outputs-score` v1.0.0

### 2a. Dimension 1 -- TIER MATCH (40 points)

```yaml
tier_match:
  weight: 40
  calculation: "match_rate = count(opus_tier == haiku_tier) / total_items"
  scoring:
    perfect_match: 40    # 100%
    high_match: 32       # 90-99%
    moderate_match: 24   # 75-89%
    low_match: 16        # 50-74%
    poor_match: 0        # <50%
  veto: "IF match_rate < 0.75 -> VETO"
```

### 2b. Dimension 2 -- SCORE VARIANCE (30 points)

```yaml
score_variance:
  weight: 30
  calculation: |
    FOR each item: variance = abs(opus - haiku) / opus * 100
    Use max_variance for scoring (worst case)
  scoring:
    within_5pct: 30
    within_10pct: 24
    within_15pct: 18
    within_20pct: 12
    beyond_20pct: 0
  veto: "IF max_variance > 25% -> VETO"
  review: "IF max_variance > 15% -> REVIEW"
```

### 2c. Dimension 3 -- CHECKPOINT MATCH (20 points)

```yaml
checkpoint_match:
  weight: 20
  calculation: "match_rate = matching_checkpoints / total_checkpoints"
  scoring:
    perfect_match: 20    # 100%
    high_match: 16       # 95-99%
    moderate_match: 12   # 90-94%
    low_match: 8         # 80-89%
    poor_match: 0        # <80%
  note: "If task has no binary checkpoints, award 20 points"
```

### 2d. Dimension 4 -- RECOMMENDATION QUALITY (10 points)

```yaml
recommendation_quality:
  weight: 10
  evaluation: "Would user take same action based on each output?"
  scoring:
    same_actions: 10
    similar_actions: 7
    different_actions: 3
    contradictory: 0
  veto: "IF contradictory -> VETO"
```

### 2e. Check Veto Conditions

| ID | Condition | Severity |
|----|-----------|----------|
| MTQ_VC_001 | Score Variance >15% | review |
| MTQ_VC_002 | Score Variance >25% | veto |
| MTQ_VC_003 | Tier Match <90% | review |
| MTQ_VC_004 | Tier Match <75% | veto |
| MTQ_VC_005 | Contradictory Recommendations | veto |

**Intermediate structure:**

```yaml
dimension_scores:
  tier_match:
    score: 0  # /40
    match_rate: "0%"
  score_variance:
    score: 0  # /30
    avg_variance: "0%"
    max_variance: "0%"
  checkpoint_match:
    score: 0  # /20
    match_rate: "0%"
  recommendation_quality:
    score: 0  # /10
    assessment: "same|similar|different|contradictory"
  total: 0  # /100
  vetos_triggered: []
  reviews_triggered: []
```

---

## Step 3: Determine Verdict & Report

> Merged from `an-compare-outputs-report` v1.0.0

### 3a. Determine Decision

```yaml
thresholds:
  QUALIFIED: ">= 85 points AND no veto triggered"
  CONDITIONAL: "70-84 points OR veto with mitigation possible"
  NOT_QUALIFIED: "< 70 points OR hard veto"
```

### 3b. Write Rationale

Explain the decision based on dimension scores and veto status. Focus on actionable outcomes.

### 3c. Generate Recommendations

```yaml
recommendations:
  if_qualified:
    - "Update model-routing.yaml: tier = haiku"
    - "Add validated: true with test_date"
  if_conditional:
    - "{Specific fixes needed}"
    - "Re-test after fixes"
  if_not_qualified:
    - "Keep tier = opus"
    - "Document root cause"
```

### 3d. Assemble & Save Report

Save to: `squads/squad-creator-pro/test-cases/{task_name}/qualification-report.yaml`

```yaml
qualification_report:
  task: "{task_name}"
  evaluation_date: "{ISO date}"
  evaluator: "opus"
  inputs:
    opus_baseline: "{path}"
    haiku_output: "{path}"
  dimension_scores:
    tier_match: { score, match_rate, details }
    score_variance: { score, avg_variance, max_variance, details }
    checkpoint_match: { score, match_rate, details }
    recommendation_quality: { score, assessment, details }
  total_score: "X/100"
  veto_conditions:
    triggered: [...]
    not_triggered: [...]
  decision: "QUALIFIED | CONDITIONAL | NOT_QUALIFIED"
  rationale: "{explanation}"
  recommendations: [...]
```

---

## Acceptance Criteria

- [ ] Both files loaded and parsed successfully
- [ ] All scored items extracted and aligned
- [ ] Structural differences noted
- [ ] Items normalized for 1:1 comparison
- [ ] All 4 dimensions scored per rubric
- [ ] Calculations are reproducible and shown
- [ ] Veto conditions checked and documented
- [ ] Total score calculated
- [ ] Decision determined using thresholds (>=85 QUALIFIED, 70-84 CONDITIONAL, <70 NOT_QUALIFIED)
- [ ] Rationale explains the decision
- [ ] Recommendations are actionable
- [ ] Report saved to `squads/squad-creator-pro/test-cases/{task_name}/qualification-report.yaml`
- [ ] Report includes all dimension details

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-compare-outputs.md` | Parent orchestrator |
