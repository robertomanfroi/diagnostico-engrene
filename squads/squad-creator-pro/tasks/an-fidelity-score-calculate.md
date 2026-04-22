---
task-id: an-fidelity-score-calculate
name: "Calculate Fidelity Score"
version: 2.0.0
execution_type: Hybrid
model: Haiku
model_rationale: "File identification and script execution are deterministic (95%). LLM only synthesizes recommendations (5%)."
haiku_eligible: true
estimated-time: 10-15 min
complexity: medium

inputs:
  required:
    - clone_path: "Path to the clone agent file"

outputs:
  primary:
    - fidelity_report: "Complete fidelity report with scores, classification, gaps, and trajectory"

worker_script: "scripts/fidelity-score.sh"
load: "data/an-clone-validation.yaml"
elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-fidelity-score-calculate
  task_name: Calculate Fidelity Score
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10-15m
  domain: Operational
  input:
  - '{''clone_path'': ''Path to the clone agent file''}'
  output:
  - '{''fidelity_report'': ''Complete report with scores, classification, gaps, and
    trajectory''}'
  action_items:
  - Identify Clone Files & Run Preflight Script
  - Validate Preflight Scores Against 8 Layer Checklists
  - Calculate Weighted Score, Classify & Generate Report
  acceptance_criteria:
  - Clone agent file located and supporting files identified
  - Worker script executed successfully
  - Preflight scores file exists and is valid YAML
  - All 8 layers have scores in preflight output
  - All 8 layers evaluated with binary checklists
  - Each layer has 5 checkpoints marked PASS or FAIL
  - Scores match preflight script output
  - Observable layers (1-4) and Deep layers (5-8) clearly separated
  - Weighted score calculated with formula
  - Classification assigned deterministically
  - Gaps listed with specific remediation
  - Report YAML generated in specified format
  - Trajectory to next milestone documented
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
  coherence_threshold: 0.95
  error_behavior: raise
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


# Task: Calculate Fidelity Score

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-fidelity-score-calculate` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `an-fidelity-score` (orchestrator)
- **Sequence:** 1 of 1 (merged from 3 subtasks in v1.0.0)
- **Previous Task:** None
- **Next Task:** None (final output)

## Purpose

Locate all clone-related files, execute the worker script to generate deterministic preflight scores, validate scores against 8 layer checklists, apply the weighted scoring formula, classify the clone version, identify gaps with specific remediation, and generate the full fidelity report.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-FS-001 | Preflight script must succeed | BLOCK - Do NOT proceed manually |

## Scoring Calibration

```yaml
scoring_philosophy:
  principle: "SCORE O QUE EXISTE, nao o que falta"
  bias_correction: "Haiku tende a sub-pontuar. Compensar sendo generoso."
  evidence_rule: "Se existe evidencia, conta ponto. Gaps vao para recommendations."
```

## Workflow / Steps

### Step 1: Identify & Preflight

#### 1.1 Locate Clone Files

1. Find the agent file (e.g., `.claude/agents/{clone}.md` or `squads/*/agents/{clone}.md`)
2. Identify supporting files:
   - `voice_dna` section
   - `thinking_dna` section
   - `heuristics` files
   - `artifacts` files

```yaml
clone_files:
  agent_file: "{path}"
  voice_dna_section: true|false
  thinking_dna_section: true|false
  heuristics_files: []
  artifacts_files: []
```

#### 1.2 Run Worker Script (MANDATORY)

```bash
bash squads/squad-creator-pro/scripts/fidelity-score.sh <clone-path> > /tmp/preflight-fidelity-score.yaml
```

**IF command fails:** FIX the script error. Do NOT proceed manually.
**IF command succeeds:** READ `/tmp/preflight-fidelity-score.yaml`. Use ONLY these scores.

#### 1.3 Validate Script Output

Confirm output file exists and contains valid YAML with scores for all 8 layers.

---

### Step 2: Validate Layers

#### 2.1 Validate Preflight Scores Against Checklists

For each of the 8 layers, confirm the script's checkpoint results:

**Layer 1: Behavioral Patterns** (Observable, weight 0.8)
- Where: `persona:`, `behavioral_patterns:`, `modes:`, `states:`
- Checkpoints: greeting ritual, response structure, modes/states, trigger responses, anti-patterns

**Layer 2: Communication Style** (Observable, weight 0.8)
- Where: `voice_dna:`, `vocabulary:`, `writing_style:`
- Checkpoints: signature phrases (3+), vocabulary always, vocabulary never, sentence structure, metaphors

**Layer 3: Routines & Habits** (Observable, weight 0.8)
- Where: `workflow:`, `steps:`, `ritual:`, `process:`
- Checkpoints: opening ritual, workflow steps, checkpoint habit, closing ritual, error handling

**Layer 4: Recognition Patterns** (Observable, weight 0.8)
- Where: `heuristics:`, `red_flags:`, `patterns:`, `recognition:`
- Checkpoints: red flags, green flags, decision rules, pattern IDs, thresholds

**Layer 5: Mental Models** (Cognitive, weight 1.0)
- Where: `thinking_dna:`, `frameworks:`, `mental_models:`
- Checkpoints: primary framework, decision architecture, named frameworks (3+), framework steps, anti-patterns

**Layer 6: Values Hierarchy** (Deep, weight 1.0)
- Where: `core_beliefs:`, `values:`, `principles:`
- Checkpoints: core beliefs (3+), what defends, what rejects, trade-offs, non-negotiables

**Layer 7: Core Obsessions** (Deep, weight 1.0)
- Where: repetition of themes, `obsessions:`, `focus:`
- Checkpoints: recurring themes (3+), named obsessions, hills to die on, mission statement, legacy thinking

**Layer 8: Productive Paradoxes** (Deep, weight 1.0)
- Where: `contradictions:`, `paradoxes:`, `tensions:`
- Checkpoints: contradictions section, named paradoxes (2+), feature not bug, context-dependent, integration note

#### 2.2 Format Layer Results

```yaml
layer_scores:
  layer_1_behavioral_patterns:
    score: 0  # 0-5
    checkpoints_passed: []
    checkpoints_failed: []
  # ... layers 2-8 ...
```

---

### Step 3: Calculate Final Score

#### 3.1 Calculate Weighted Score

```python
# Observable layers (weight 0.8)
L1 = behavioral_patterns_score  # 0-5
L2 = communication_style_score  # 0-5
L3 = routines_habits_score      # 0-5
L4 = recognition_patterns_score # 0-5

# Deep layers (weight 1.0)
L5 = mental_models_score        # 0-5
L6 = values_hierarchy_score     # 0-5
L7 = core_obsessions_score      # 0-5
L8 = productive_paradoxes_score # 0-5

observable_raw = (L1 + L2 + L3 + L4)       # max 20
observable_weighted = observable_raw * 0.8   # max 16

deep_raw = (L5 + L6 + L7 + L8)             # max 20
deep_weighted = deep_raw * 1.0              # max 20

total_weighted = observable_weighted + deep_weighted  # max 36
percentage = (total_weighted / 36) * 100
```

#### 3.2 Classify (Deterministic)

| Percentage | Classification | Version |
|------------|----------------|---------|
| 0-59% | Incomplete | V0.x |
| 60-74% | Basic | V1.0 |
| 75-84% | Intermediate | V2.0 |
| 85-92% | Premium | V3.0 |
| 93-100% | Elite | V3.5+ |

#### 3.3 Identify Gaps

For each layer with score < 4:
- Which checkpoint failed
- Where to add (file section)
- Example of what it should look like

#### 3.4 Generate Report (LLM: synthesize recommendations)

```yaml
fidelity_report:
  clone: "{name}"
  clone_file: "{path}"
  date: "{ISO date}"
  scores:
    observable:
      behavioral_patterns: { score, passed, failed }
      communication_style: { score, passed, failed }
      routines_habits: { score, passed, failed }
      recognition_patterns: { score, passed, failed }
      subtotal_raw: 0
      subtotal_weighted: 0
    deep:
      mental_models: { score, passed, failed }
      values_hierarchy: { score, passed, failed }
      core_obsessions: { score, passed, failed }
      productive_paradoxes: { score, passed, failed }
      subtotal_raw: 0
      subtotal_weighted: 0
    overall:
      total_weighted: 0
      max_possible: 36
      percentage: "0%"
      classification: ""
      version: "V0.0"
  gaps:
    - layer: ""
      checkpoint_failed: 0
      checkpoint_name: ""
      what_to_add: ""
      where_to_add: ""
      example: ""
  trajectory:
    current_version: ""
    next_milestone: ""
    gaps_to_close: 0
    estimated_effort: ""
```

## Output

```yaml
fidelity_report: { complete report as above }
```

## Acceptance Criteria

- [ ] Clone agent file located and supporting files identified
- [ ] Worker script executed successfully
- [ ] Preflight scores file exists and is valid YAML with all 8 layers
- [ ] All 8 layers evaluated with binary checklists
- [ ] Each layer has 5 checkpoints marked PASS or FAIL
- [ ] Scores match preflight script output
- [ ] Observable layers (1-4) and Deep layers (5-8) clearly separated
- [ ] Weighted score calculated with formula
- [ ] Classification assigned deterministically
- [ ] Gaps listed with specific remediation
- [ ] Report YAML generated in specified format
- [ ] Trajectory to next milestone documented

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-fidelity-score.md` | Parent orchestrator |
| `checklists/mind-validation.md` | Validation checklist |
