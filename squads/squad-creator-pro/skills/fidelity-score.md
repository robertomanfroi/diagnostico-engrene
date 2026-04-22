---
name: fidelity-score
description: |
  Deterministic fidelity scoring for mind clones. Evaluates a clone agent file
  across 8 cognitive layers (4 Observable + 4 Deep) using a bash worker script,
  then classifies the clone version and identifies gaps with remediation.
  95% deterministic via scripts/fidelity-score.sh -- LLM only synthesizes
  gap recommendations. Use when: "score clone", "fidelity check",
  "how good is this clone", "avaliar fidelidade", "*fidelity-score".

model: haiku
model_rationale: "Orchestrator stub -- delegates to 3 atomic sub-tasks. 95% deterministic via worker script."
---

# /fidelity-score {clone_path}

Evaluate the cognitive fidelity of a mind clone agent file across 8 layers and produce a scored report with classification, gaps, and remediation trajectory.

## INPUT

```
$ARGUMENTS = absolute path to the clone agent file (e.g., squads/squad-creator-pro/agents/oalanicolas.md)
```

## WHEN TO USE

- After completing a mind clone extraction (wf-clone-mind)
- Before marking a clone as production-ready
- When iterating on clone quality (gap remediation cycle)
- When comparing clone versions over time
- Standalone scoring invoked via `*fidelity-score` command

## CONTRACT

### Inputs

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| clone_path | path | YES | Path to the clone agent file to evaluate |

### Outputs

| Field | Type | Description |
|-------|------|-------------|
| score | number (0-100) | Overall fidelity percentage (weighted) |
| classification | enum | Incomplete (V0.x) / Basic (V1.0) / Intermediate (V2.0) / Premium (V3.0) / Elite (V3.5+) |
| layers | array | Per-layer breakdown: 8 layers x 5 checkpoints each (PASS/FAIL with evidence) |
| gaps | array | Identified deficiencies with checkpoint name, where to add, and example |
| trajectory | object | Current version, next milestone, gaps to close, estimated effort |
| verdict | string | Summary recommendation for next action |

### Veto Conditions

| ID | Condition | Behavior |
|----|-----------|----------|
| VETO-FID-001 | clone_path does not exist | BLOCK -- file not found, do not execute |
| VETO-FID-002 | scripts/fidelity-score.sh not found or not executable | BLOCK -- worker script missing |
| VETO-FID-003 | Score is estimated or manually assigned instead of calculated | BLOCK -- must run script, never score manually |

## EXECUTION PROTOCOL

### Step 1: Preflight Validation

1. Verify `$ARGUMENTS` (clone_path) file exists on disk
2. Verify `squads/squad-creator-pro/scripts/fidelity-score.sh` is accessible
3. If either check fails, report which VETO condition triggered and HALT

### Step 2: Run Deterministic Worker Script

```bash
bash squads/squad-creator-pro/scripts/fidelity-score.sh {clone_path} > /tmp/preflight-fidelity-score.yaml
```

- IF command fails: Report the script error. Do NOT proceed manually. Do NOT estimate scores
- IF command succeeds: Read `/tmp/preflight-fidelity-score.yaml` and use ONLY these scores

### Step 3: Parse and Structure Script Output

The script outputs YAML with 8 layer sections plus a summary. Parse each section:

```yaml
# Script outputs these sections:
layer_1_behavioral_patterns:    # Observable, weight 0.8
  score: 0-5
  checkpoints: [{id, name, result: PASS|FAIL}]

layer_2_communication_style:    # Observable, weight 0.8
layer_3_routines_habits:        # Observable, weight 0.8
layer_4_recognition_patterns:   # Observable, weight 0.8
layer_5_mental_models:          # Deep, weight 1.0
layer_6_values_hierarchy:       # Deep, weight 1.0
layer_7_core_obsessions:        # Deep, weight 1.0
layer_8_productive_paradoxes:   # Deep, weight 1.0

summary:
  observable: {raw, weighted}
  deep: {raw, weighted}
  total: {weighted, percentage, classification}
```

Extract per-layer scores and checkpoint results directly from the parsed output.

### Step 4: Apply Classification (Deterministic)

Use the percentage from the script summary. Classification thresholds:

| Percentage | Classification | Version |
|------------|----------------|---------|
| 0-59% | Incomplete | V0.x |
| 60-74% | Basic | V1.0 |
| 75-84% | Intermediate | V2.0 |
| 85-92% | Premium | V3.0 |
| 93-100% | Elite | V3.5+ |

### Step 5: Identify Gaps (LLM: 5% of work)

For each layer with score < 4/5, generate gap entries:

```yaml
gaps:
  - layer: "Layer N: {name}"
    checkpoint_failed: {id}
    checkpoint_name: "{name}"
    what_to_add: "Description of what content is missing"
    where_to_add: "Section in the clone file where it should be added"
    example: "Brief example of expected content"
```

### Step 6: Generate Trajectory

```yaml
trajectory:
  current_version: "{classification version}"
  next_milestone: "{next classification tier}"
  gaps_to_close: {count of gaps}
  estimated_effort: "{time estimate based on gap count}"
```

### Step 7: Escalation

- Score < 60 (Incomplete) --> Flag for manual review by @oalanicolas before clone is considered production-ready
- gaps > 3 --> List all gaps explicitly with remediation suggestions
- Any VETO triggered --> Report which condition failed, stop execution immediately

## SCORING PHILOSOPHY

```yaml
scoring_philosophy:
  principle: "SCORE O QUE EXISTE, nao o que falta"
  bias_correction: "Haiku tende a sub-pontuar. Compensar sendo generoso."
  evidence_rule: "Se existe evidencia, conta ponto. Gaps vao para recommendations."
```

## OUTPUT FORMAT

```yaml
# Fidelity Score Report
clone: "{name}"
clone_file: "{path}"
timestamp: "{ISO timestamp}"

scores:
  observable:
    behavioral_patterns: {score: N, passed: [...], failed: [...]}
    communication_style: {score: N, passed: [...], failed: [...]}
    routines_habits: {score: N, passed: [...], failed: [...]}
    recognition_patterns: {score: N, passed: [...], failed: [...]}
    subtotal_raw: N/20
    subtotal_weighted: N/16
  deep:
    mental_models: {score: N, passed: [...], failed: [...]}
    values_hierarchy: {score: N, passed: [...], failed: [...]}
    core_obsessions: {score: N, passed: [...], failed: [...]}
    productive_paradoxes: {score: N, passed: [...], failed: [...]}
    subtotal_raw: N/20
    subtotal_weighted: N/20
  overall:
    total_weighted: N/36
    max_possible: 36
    percentage: "N%"
    classification: "{Incomplete|Basic|Intermediate|Premium|Elite}"
    version: "VX.X"

gaps:
  - layer: ""
    checkpoint_failed: N
    checkpoint_name: ""
    what_to_add: ""
    where_to_add: ""
    example: ""

trajectory:
  current_version: ""
  next_milestone: ""
  gaps_to_close: N
  estimated_effort: ""

verdict: "{summary recommendation}"
```

## ACCOUNTABILITY

- **Owner:** @oalanicolas
- **Escalation:** Score < 60 requires human review before clone is considered production-ready
- **Audit trail:** Output must be saved to `squads/squad-creator-pro/test-cases/an-fidelity-score/` with timestamp
- **Checklist reference:** Verify against `squads/squad-creator-pro/checklists/mind-validation.md`

## PIPELINE REFERENCE

This skill wraps the 3-phase atomic task pipeline:

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `an-fidelity-score-identify` | Identify Clone Files & Run Script | 5 min |
| 2 | `an-fidelity-score-layers` | Execute 8 Layer Checklists | 5 min |
| 3 | `an-fidelity-score-calculate` | Calculate Score, Classify & Report | 5 min |

## WEIGHTED SCORE FORMULA

```python
# Observable layers (weight 0.8)
observable_raw = L1 + L2 + L3 + L4          # max 20
observable_weighted = observable_raw * 0.8   # max 16

# Deep layers (weight 1.0)
deep_raw = L5 + L6 + L7 + L8               # max 20
deep_weighted = deep_raw * 1.0              # max 20

# Final
total_weighted = observable_weighted + deep_weighted  # max 36
percentage = (total_weighted / 36) * 100
```

## COST OPTIMIZATION

This skill runs on **Haiku** (~$0.25/1M input, $1.25/1M output).
95% of the scoring is deterministic via bash script -- cost effectively $0.
LLM cost is only for gap synthesis: ~2K tokens input, ~500 tokens output = ~$0.001 per evaluation.

---

*Skill: fidelity-score v1.0*
*Model: haiku (enforced)*
*Worker: scripts/fidelity-score.sh*
*Tasks: an-fidelity-score (orchestrator) + 3 atomic sub-tasks*
