# Task: QA Check Completeness

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-check-completeness` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: qa-check-completeness
name: QA Check Completeness
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Check completeness of a created component against Definition of Done
  criteria. Runs quality scoring with weighted criteria per component type
  and produces a numeric score (0-10).
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qa_check_completeness
Output: artifact::qa_check_completeness
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Evaluate the qualitative completeness of a component beyond structural and schema correctness. This task answers: "Is this component good enough to ship?" by scoring it against weighted quality criteria specific to each component type.

## Prerequisites

- [ ] qa-check-structure has passed
- [ ] qa-check-schema has passed
- [ ] qa-check-references has passed
- [ ] `data/quality-dimensions-framework.md` accessible

## Inputs

```yaml
inputs:
  - name: created_component
    type: string
    required: true
    description: "Path to created component"

  - name: component_type
    type: enum
    required: true
    values: ["squad", "agent", "task", "workflow", "template"]
    description: "Type of component created"

  - name: references_result
    type: object
    required: true
    source: qa-check-references
    description: "Result from references check (must be PASS)"
```

## Workflow

### Step 1: Select Quality Criteria

Load scoring criteria based on `component_type`:

**For squads:**

Run `validate-squad {squad_name}` and extract:
- Tier 1 result (structural)
- Tier 2 result (schema)
- Tier 3 score (quality)
- Tier 4 score (depth)
- Final score
- Veto triggered (boolean)

**For agents:**

| Criterion | Weight | Checks |
|-----------|--------|--------|
| Persona completeness | 0.20 | role, style, identity, focus defined |
| Commands functionality | 0.20 | *help exists, commands map to capabilities |
| Voice consistency | 0.15 | voice_dna present (if Expert), vocabulary used |
| Examples quality | 0.15 | output_examples present, realistic |
| Dependencies valid | 0.15 | all references exist (from qa-check-references) |
| Documentation | 0.15 | whenToUse clear, description helpful |

**For tasks:**

| Criterion | Weight | Checks |
|-----------|--------|--------|
| Task Anatomy complete | 0.25 | 8 required fields present |
| Prompt quality | 0.25 | specific, includes examples, anti-patterns |
| Validation defined | 0.20 | success criteria, failure handling |
| Integration | 0.15 | references valid, outputs defined |
| Documentation | 0.15 | purpose clear, usage examples |

**For workflows:**

| Criterion | Weight | Checks |
|-----------|--------|--------|
| Phase completeness | 0.30 | all phases have tasks, inputs, outputs |
| Sequence validity | 0.25 | no collisions, output-input chain valid |
| Error handling | 0.20 | failure paths defined |
| Documentation | 0.25 | purpose, usage, examples |

### Step 2: Score Each Criterion

For each criterion:
1. Run the specified checks
2. Calculate a score (0.0 to 1.0) based on how many checks pass
3. Multiply by weight to get weighted score
4. Sum all weighted scores and scale to 0-10

### Step 3: Apply Thresholds

| Score | Verdict | Meaning |
|-------|---------|---------|
| >= 7.0 | PASS | Component is ready for delivery |
| >= 5.0 and < 7.0 | CONDITIONAL | Component has issues but may proceed |
| < 5.0 | FAIL | Component requires fixes before delivery |

### Step 4: Compile Results

```yaml
completeness_result:
  final_score: X.X
  verdict: "PASS | CONDITIONAL | FAIL"
  breakdown:
    - criterion: "Persona completeness"
      weight: 0.20
      score: 0.85
      weighted: 1.70
      details: "Missing: focus field"
    - criterion: "Commands functionality"
      weight: 0.20
      score: 1.00
      weighted: 2.00
      details: "All checks passed"
  veto_triggered: false
```

## Output

```yaml
output:
  name: completeness_result
  type: object
  description: "Quality scoring results with per-criterion breakdown"
  passed_to: qa-generate-report
```

## Acceptance Criteria

- [ ] Correct criteria loaded per component type
- [ ] Each criterion scored independently with weighted calculation
- [ ] Final score is on 0-10 scale
- [ ] Threshold verdicts applied correctly (PASS/CONDITIONAL/FAIL)
- [ ] Breakdown includes per-criterion detail
- [ ] For squads, validate-squad is invoked and results extracted

### Step 5: Doom Loop Awareness (Advisory)

**[STORY-109.1] AC10 -- Advisory dimension, does NOT change existing scoring values.**

After computing the final score, run an advisory doom-loop awareness check:

```yaml
doom_loop_awareness:
  type: advisory
  weight: 0.00        # Does NOT affect the numeric score
  penalty: -0.5       # Applied ONLY as a warning annotation, not to final_score
  check: |
    Verify that the component (especially workflows) includes
    at least one of the following doom-loop mitigations:
    - max_retries or circuit_breaker defined in error_handling
    - Reference to doom-loop-detector.js in scripts
    - Explicit retry limit on checkpoint failures
  scoring:
    has_mitigation: "No penalty -- doom loop aware"
    no_mitigation: "Advisory penalty -0.5 noted in report (does NOT reduce final_score)"
```

This dimension is informational only. It appears in the completeness_result breakdown
with `advisory: true` and never changes the numeric score or existing criterion values.

## Veto Conditions

| Condition | Action |
|-----------|--------|
| validate-squad reports veto_triggered | FAIL regardless of score |
| Score < 5.0 | FAIL -- component not ready |
| Any criterion scores 0.0 | FAIL -- critical gap detected |

## Related Documents

| Document | Purpose |
|----------|---------|
| `qa-after-creation.md` | Parent orchestrator task |
| `validate-squad.md` | Called for squad-type components |
| `data/quality-dimensions-framework.md` | Quality criteria definitions |
| `qa-generate-report.md` | Consumes this task's output |
