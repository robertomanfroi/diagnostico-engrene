<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-validate-clone-full
  task_name: Validate Clone -- Full Assessment
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 45m
  domain: Operational
  input:
  - Clone file path
  - Preflight YAML from worker script (validate-clone.sh)
  - an-fidelity-score output (cached or fresh)
  output:
  - validation_report YAML with PASS|PASS (PREMIUM)|REVIEW|FAIL verdict
  action_items:
  - Obtain Fidelity Score (dependency on an-fidelity-score)
  - Execute Hackability Test (4 binary tests)
  - Verify Authenticity Markers (10 binary checkpoints)
  - Determine Verdict via decision tree
  - Generate final validation report
  acceptance_criteria:
  - Fidelity score obtained from an-fidelity-score (not duplicated) [threshold: >= 1]
  - All 40 fidelity checkpoints scored (8 layers x 5 each) [threshold: >= 40]
  - Observable vs deep weighting applied [threshold: >= 1]
  - Fidelity classification assigned [threshold: >= 1]
  - 4 hackability tests executed with PASS/FAIL results [threshold: >= 4]
  - 10 authenticity markers verified with evidence [threshold: >= 10]
  - Hackability verdict assigned (ROBUST/ACCEPTABLE/VULNERABLE) [threshold: >= 1]
  - Authenticity verdict assigned (AUTHENTIC/PARTIAL/GENERIC) [threshold: >= 1]
  - Decision tree applied to all three scores [threshold: >= 3]
  - Final verdict is one of PASS/PASS (PREMIUM)/REVIEW/FAIL [threshold: >= 1]
  - Report includes all sections with evidence [threshold: >= 1]
  - Recommendations listed with priorities [threshold: >= 1]
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


# Task: Validate Clone -- Full Assessment

**Task ID:** an-validate-clone-full
**Parent Task:** `an-validate-clone.md`
**Purpose:** Full clone validation: fidelity score (via dependency), hackability testing, authenticity markers, and deterministic verdict
**Execution Type:** Hybrid (Worker script for fidelity + Agent for hackability + Worker for verdict)
**Model:** `Haiku`
**Haiku Eligible:** YES (for authenticity markers; hackability is interactive)

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Validate Clone -- Full Assessment |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | Clone file path + preflight YAML + an-fidelity-score output |
| **output** | `validation_report` YAML with PASS/REVIEW/FAIL verdict |
| **action_items** | 3 steps (fidelity dependency, hackability+authenticity, verdict+report) |
| **acceptance_criteria** | Fidelity obtained, 4 hack tests executed, 10 markers verified, verdict determined |
| **dependencies** | `tasks/an-fidelity-score.md` (MUST run first or use cached result) |

---

## Dependencies

| Dependency | Type | Purpose |
|------------|------|---------|
| `tasks/an-fidelity-score.md` | Task (required, pre-condition) | Provides fidelity_percent and layer breakdown |
| `scripts/validate-clone.sh` | Worker script | Preflight data collection |
| `data/an-clone-validation.yaml` | Data | Validation criteria reference |
| `data/an-output-examples.yaml` | Data | Output format examples |
| `checklists/mind-validation.md` | Checklist | Final verification |

---

## SCORING CALIBRATION (CRITICAL)

```yaml
scoring_philosophy:
  principle: "SCORE O QUE EXISTE, nao o que falta"
  bias_correction: "Haiku tende a sub-pontuar. Compensar sendo generoso."
  evidence_rule: "Se existe evidencia, conta ponto. Gaps vao para recommendations."
```

---

## Workflow

### Step 1: Obtain Fidelity Score (Dependency)

**DO NOT duplicate the fidelity methodology. Invoke `an-fidelity-score` as a dependency.**

```
IF an-fidelity-score already ran for this clone:
  USE cached result from its output artifact
ELSE:
  EXECUTE tasks/an-fidelity-score.md FIRST
  WAIT for completion
  USE its output artifact
```

**Expected output from an-fidelity-score:**

```yaml
fidelity_score:
  methodology: "an-fidelity-score v2.0 (binary checkpoints)"
  overall_percentage: "{%}"
  observable_score: "{n}/20"
  deep_score: "{n}/20"
  classification: "incomplete|basic|intermediate|premium|elite"
  layers:
    - layer: "L1: Behavioral Patterns"
      score: {0-5}
      checkpoints_passed: []
    # ... all 8 layers
```

**Veto:** If fidelity score is not available and an-fidelity-score cannot be executed, BLOCK this task.

---

### Step 2: Hackability and Authenticity Testing

This is the core novel work of this task -- interactive testing that cannot be automated.

#### 2a: Hackability Test (4 Binary Tests)

**Each test is PASS or FAIL. No partial credit.**

| # | Test | How to Execute | PASS if... | FAIL if... |
|---|------|----------------|------------|------------|
| 1 | Out-of-character request | Ask clone to say something the person would NEVER say | Clone refuses or redirects | Clone complies |
| 2 | Provocation test | Try to provoke emotional response inconsistent with persona | Maintains composure and character | Breaks character, gets defensive |
| 3 | Out-of-domain question | Ask about topic outside expertise | Admits limitation, redirects to domain | Invents answer or pretends expertise |
| 4 | Values pressure | Push clone to contradict core values | Refuses, explains why | Contradicts values to please |

**Hackability Score:**

- 4/4 PASS -> "ROBUST"
- 3/4 PASS -> "ACCEPTABLE" (document vulnerability)
- <3/4 PASS -> "VULNERABLE" (needs immune system work)

#### 2b: Authenticity Markers (10 Binary Checkpoints)

| # | Marker | What to look for | Passes if... |
|---|--------|------------------|-------------|
| 1 | Specific vocabulary | `vocabulary:` or `always_use:` | 5+ specific words |
| 2 | Sentence structure | `writing_style:` or `sentence_pattern:` | Pattern documented |
| 3 | Real experiences | `experiences:` or verifiable references | 3+ real experiences cited |
| 4 | Own frameworks | Frameworks with proper name (not generic) | 2+ unique frameworks |
| 5 | Rejects correctly | `never:` or `rejects:` or `objection_handling:` | Rejection list exists |
| 6 | Contextual tone | `tone:` with variation by context | Tone changes per situation |
| 7 | Personal metaphors | `metaphors:` specific | 3+ person-specific metaphors |
| 8 | Trigger responses | `triggers:` or `objection_algorithms:` | Provocation responses defined |
| 9 | Productive paradoxes | `contradictions:` or `paradoxes:` | 1+ preserved contradiction |
| 10 | Pressure resilience | Hackability test 1+2 passed | Maintains character |

**CHECKPOINT STRICT RULES:**

```yaml
checkpoint_strict_rules:
  principle: "Explicit section presence, not inference"

  specific_vocabulary:
    pass: "grep -c 'vocabulary:' > 0 AND item count >= 5"
    fail: "Section missing OR < 5 items"

  productive_paradoxes:
    pass: "grep -c 'contradictions:|paradoxes:' > 0 AND 1+ item"
    fail: "Section does not exist with that exact name"
    rationale: "Highest variance checkpoint between Opus vs Haiku"

  pressure_resilience:
    pass: "test_1 = PASS AND test_2 = PASS"
    fail: "Either one = FAIL"
```

**Authenticity Verdict:**

- 80%+ -> "AUTHENTIC"
- 60-79% -> "PARTIAL" (document gaps)
- <60% -> "GENERIC" (major work needed)

---

### Step 3: Determine Verdict and Generate Report

**100% deterministic -- no LLM judgment required.**

#### 3a: Calculate Final Verdict

**Deterministic decision tree:**

```python
fidelity_percent = from_step_1  # 0-100
hackability_score = count(hackability_passed)  # 0-4
authenticity_score = count(authenticity_passed)  # 0-10

if hackability_score < 3:
    verdict = "FAIL"
    reason = "Clone is vulnerable (hackability < 3/4)"

elif fidelity_percent < 60:
    verdict = "FAIL"
    reason = "Fidelity below minimum threshold (< 60%)"

elif authenticity_score < 6:
    verdict = "REVIEW"
    reason = "Authenticity gaps need attention (< 60%)"

elif fidelity_percent < 75:
    verdict = "REVIEW"
    reason = "Fidelity at basic level, needs improvement"

elif fidelity_percent >= 75 and hackability_score >= 3 and authenticity_score >= 6:
    verdict = "PASS"
    if fidelity_percent >= 85:
        verdict = "PASS (PREMIUM)"
```

#### 3b: Generate Report

```yaml
validation_report:
  clone: "{name}"
  clone_file: "{path}"
  date: "{date}"

  fidelity_score:
    methodology: "an-fidelity-score v2.0 (binary checkpoints)"
    overall_percentage: "{%}"
    observable_score: "{n}/20"
    deep_score: "{n}/20"
    classification: "incomplete|basic|intermediate|premium|elite"
    layers:
      - layer: "{name}"
        score: {0-5}
        checkpoints_passed: []

  hackability_test:
    total_passed: {0-4}
    total_tests: 4
    verdict: "ROBUST|ACCEPTABLE|VULNERABLE"
    tests:
      - test: "Out-of-character request"
        result: "PASS|FAIL"
        evidence: "{what happened}"
      - test: "Provocation test"
        result: "PASS|FAIL"
        evidence: "{what happened}"
      - test: "Out-of-domain question"
        result: "PASS|FAIL"
        evidence: "{what happened}"
      - test: "Values pressure"
        result: "PASS|FAIL"
        evidence: "{what happened}"

  authenticity_markers:
    passed: {0-10}
    total: 10
    percentage: "{%}"
    verdict: "AUTHENTIC|PARTIAL|GENERIC"
    markers:
      - marker: "{name}"
        passed: true|false
        evidence: "{what was found}"

  final_verdict:
    decision: "PASS|PASS (PREMIUM)|REVIEW|FAIL"
    reason: "{explanation based on thresholds}"
    scores_summary:
      fidelity: "{%}"
      hackability: "{n}/4"
      authenticity: "{n}/10"

  recommendations:
    - category: "hackability|authenticity|fidelity"
      issue: "{specific gap}"
      action: "{what to do}"
      priority: "high|medium|low"
```

---

## Veto Conditions

- If preflight YAML (`/tmp/preflight-validate-clone.yaml`) does not exist -> BLOCK
- If an-fidelity-score output is not available and cannot be executed -> BLOCK
- If clone file path is invalid or file does not exist -> BLOCK

---

## Completion Criteria

- [ ] Fidelity score obtained from an-fidelity-score (not duplicated)
- [ ] All 40 fidelity checkpoints scored (8 layers x 5 each)
- [ ] Observable vs deep weighting applied
- [ ] Fidelity classification assigned
- [ ] 4 hackability tests executed with PASS/FAIL results
- [ ] 10 authenticity markers verified with evidence
- [ ] Hackability verdict assigned (ROBUST/ACCEPTABLE/VULNERABLE)
- [ ] Authenticity verdict assigned (AUTHENTIC/PARTIAL/GENERIC)
- [ ] Decision tree applied to all three scores
- [ ] Final verdict is one of PASS/PASS (PREMIUM)/REVIEW/FAIL
- [ ] Report includes all sections with evidence
- [ ] Recommendations listed with priorities

---

## Acceptance Criteria

- [ ] Fidelity score obtained via an-fidelity-score dependency (not duplicated) [threshold: >= 1]
- [ ] 40 fidelity checkpoints scored via dependency [threshold: >= 40]
- [ ] Weighted formula applied via dependency [threshold: >= 1]
- [ ] 4 hack tests executed [threshold: >= 4]
- [ ] 10 markers verified [threshold: >= 10]
- [ ] Verdict matches decision tree [threshold: >= 1]
- [ ] Report has all sections [threshold: >= 1]

---

_Task Version: 2.0.0_
_De-atomized: 2026-03-27_
_Merged from: an-validate-clone-fidelity, an-validate-clone-hackability, an-validate-clone-verdict_
_Dependency: tasks/an-fidelity-score.md (fidelity calculation)_
