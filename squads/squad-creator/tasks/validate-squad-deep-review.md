# Task: Validate Squad — Deep Review

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-deep-review` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: validate-squad-deep-review
name: "Validate Squad Deep Review"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Optional CLI-assisted semantic review using canonical input pack. Scores quality dimensions beyond deterministic checks."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::validate_squad_deep_review
Output: artifact::validate_squad_deep_review
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Perform deep semantic analysis of squad quality using reviewer CLI (Claude/Codex) when available. This phase is OPTIONAL -- quick mode skips it entirely. The review scores semantic dimensions that deterministic scripts cannot evaluate: prompt quality, pipeline coherence, checklist actionability, documentation depth, and executor optimization.

## Prerequisites

- [ ] Preflight passed (`validate-squad-preflight` status = PASS)
- [ ] Type detected (`validate-squad-classify` completed)
- [ ] `/tmp/preflight-results.yaml` exists (deterministic base layer)
- [ ] Reviewer CLI available (`claude -p` or `codex exec --json`)

## Atomic Script

The deep review phase is available as a standalone script:

```bash
# Run deep review (requires Claude CLI)
bash squads/squad-creator/scripts/validate-squad-deep.sh squads/{squad_name}/ [--model opus|haiku] [--verbose]
```

The script checks for Claude CLI availability and exits gracefully with `{"status": "SKIPPED"}` if not found. Output is JSON to stdout.

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
  detected_type:
    type: string
    required: true
    description: "From type-detect output"
  preflight_results:
    type: file
    required: true
    path: "/tmp/preflight-results.yaml"
  mode:
    type: string
    required: false
    default: "deep"
    description: "deep (full review) or quick (skip this task)"
```

## Workflow / Steps

### Step 0: Mode Check

If `mode == quick`, emit a skip result and exit. Quick mode relies on deterministic scoring only.

### Step 1: Assemble Canonical Input Pack

Every deep review MUST receive the same canonical pack:

- `config.yaml` completo
- Entry agent canonical file (from config.yaml `entry_agent`)
- Canonical workflow file (from `workflows/`)
- 2-4 representative tasks from the validated flow
- Deterministic findings from preflight
- Base metrics (`agents_count`, `tasks_count`, `checklists_count`, `total_lines`)

**VETO:** Never use `find ... | head -1` for agent/workflow selection. Never review only arbitrary samples when a canonical asset is defined.

### Step 2: Score Semantic Dimensions

#### 2.1 Prompt Quality (25%)

Sample 3 representative tasks (most complex, entry/main, random). Score each on:

| Criterion | Points |
|-----------|--------|
| Explicit examples (input/output) | 3 |
| Anti-patterns ("don't do" section) | 2 |
| Measurable success criteria | 2 |
| Step-by-step sequential instructions | 2 |
| No vague language ("verify", "ensure" without specifics) | 1 |

Per-task max: 10. Final: average of 3 sampled tasks.

#### 2.2 Pipeline Coherence (25%)

| Criterion | Points |
|-----------|--------|
| Output->Input chain consistency across phases | 3 |
| No sequence number collisions | 2 |
| Checkpoints at critical points | 2 |
| Failure/rework handling defined | 2 |
| Dependencies explicit (not implicit) | 1 |

#### 2.3 Checklist Actionability (25%)

Evaluate all checklists (max 3). Score each on:

| Criterion | Points |
|-----------|--------|
| Items answerable YES/NO | 3 |
| Scoring system with point values | 2 |
| Pass/fail thresholds defined | 2 |
| Auto-correction guidance on failure | 2 |
| Edge case coverage | 1 |

#### 2.4 Documentation (25%)

Binary checks (0 or 1 each, max 10):

- README exists
- README > 100 lines
- README has activation/quick-start section
- README has command list
- Architecture doc exists
- Config has version (semver)
- Changelog exists as separate file
- Config has changelog section
- Agent documentation depth (avg > 500 lines)
- Error handling documented somewhere

#### 2.5 Optimization Opportunities (informational, not scored)

Identify tasks marked Agent that could be Worker per executor decision tree. Calculate potential savings. This is informational -- does not affect score.

### Step 3: Reviewer Decision Rules

- Reviewer CLI may classify a deterministic finding as `REAL`, `FALSE_POSITIVE`, or `NEEDS_HUMAN`.
- Any reclassification MUST include `evidence`, `why`, and `recommended_fix`.
- Reviewer CLI may lower score for semantic debt even when deterministic gates pass.
- Reviewer CLI may NOT erase broken references, missing required files, or confirmed secret material.

### Step 4: Type-Specific Contextual Validation

Based on `detected_type`, apply the relevant contextual checks:

**Expert squads:** voice_dna (30%), objection_algorithms (25%), output_examples (25%), tier_organization (20%)

**Pipeline squads:** workflow_definition (30%), phase_checkpoints (30%), orchestrator_completeness (25%), intermediate_outputs (10%), automation_script (15% if phases >= 8)

**Hybrid squads:** persona_profile (15%), behavioral_states (15%), heuristic_validation (20%), process_standards (15%), executor_decision_tree (35%)

## Output

```yaml
output:
  schema:
    status: "REVIEWED | SKIPPED"
    mode: "deep | quick"
    semantic_scores:
      prompt_quality: 0.0-10.0
      pipeline_coherence: 0.0-10.0
      checklist_actionability: 0.0-10.0
      documentation: 0.0-10.0
    contextual_score: 0.0-10.0
    contextual_breakdown: {...}
    reclassifications:
      - finding_id: "..."
        verdict: "REAL | FALSE_POSITIVE | NEEDS_HUMAN"
        evidence: "..."
    optimization:
      convertible_tasks: N
      potential_savings: "~$X/month"
```

## Acceptance Criteria

- [ ] Canonical input pack assembled with correct canonical assets (not random samples)
- [ ] All 4 semantic dimensions scored independently
- [ ] Type-specific contextual validation applied correctly
- [ ] Reclassifications include evidence and reasoning
- [ ] Reviewer CLI cannot overrule deterministic blockers
- [ ] Quick mode skips gracefully with SKIPPED status

## Veto Conditions

- Preflight results missing -> VETO (cannot review without deterministic base)
- Canonical input pack incomplete (no config.yaml or no entry agent) -> VETO

## Related Documents

- `validate-squad.md` (parent composed task)
- `validate-squad-preflight.md` (provides deterministic base)
- `validate-squad-classify.md` (provides type + compliance for contextual checks)
- `validate-squad-verdict.md` (consumes deep review output)
- `data/quality-dimensions-framework.md`
- `data/executor-decision-tree.md`
