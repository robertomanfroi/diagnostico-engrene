---
task-id: validate-extraction-adversarial
name: "Cross-Source Patterns & Adversarial Tests"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Adversarial reasoning requires deep semantic judgment. Not deterministic."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - checklist_results: "Results from Phase 1"
    - extraction_files: "Arquivos de extracao"

outputs:
  primary:
    - cross_source_patterns: "Confirmed patterns across 3+ sources"
    - adversarial_results: "Steel Man/Attack results per finding"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-extraction-adversarial
  task_name: Cross-Source Patterns & Adversarial Tests
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''checklist_results'': ''Results from Phase 1''}'
  - '{''extraction_files'': ''Arquivos de extracao''}'
  output:
  - '{''cross_source_patterns'': ''Confirmed patterns across 3+ sources''}'
  - '{''adversarial_results'': ''Steel Man/Attack results per finding''}'
  action_items:
  - Cross-Source Pattern Detection (Item 10)
  - Adversarial Stress Test (Item 11)
  - Clean Up Results
  acceptance_criteria:
  - At least 1 pattern confirmed across 3+ independent sources
  - At least 1 finding per lens passed adversarial test
  - DESTROYED findings removed from output
  - WEAKENED findings marked with [NEEDS_VALIDATION]
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


# Task: Cross-Source Patterns & Adversarial Tests

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-extraction-adversarial` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `validate-extraction` (orchestrator stub)
- **Sequence:** Phase 2 of 3
- **Previous Task:** `validate-extraction-checklist`
- **Next Task:** `validate-extraction-gate`

## Purpose

Validate checklist items 10 (Cross-Source Pattern Detection) and 11 (Adversarial Stress Test) which require deep semantic reasoning.

## Workflow / Steps

### Step 1: Cross-Source Pattern Detection (Item 10)

Find the same finding (gap, inversion, or evasion) appearing in 3+ INDEPENDENT sources.

```yaml
cross_source_patterns:
  - pattern: "{description}"
    type: "GAP | INVERSION | EVASION"
    sources:
      - source: "{fonte 1}"
        evidence: "{trecho}"  # [SOURCE: minuto/pagina]
      - source: "{fonte 2}"
        evidence: "{trecho}"
      - source: "{fonte 3}"
        evidence: "{trecho}"
    confidence: "CONFIRMED (3+ fontes)"
    implication: "{what the pattern reveals about the expert}"
```

**Rules:**
- If total sources < 3: mark as `[UNCONFIRMED]`, do not count as PASS
- Sources derived from each other (book based on podcast) count as 1
- Sources must be INDEPENDENT (different periods, contexts, interviewers)

### Step 2: Adversarial Stress Test (Item 11)

For each finding from the 3 lenses, apply:

1. **Steel Man** -- Strengthen the finding (strongest interpretation)
2. **Attack** -- Try to destroy it (what counter-evidence exists)
3. **Verdict** -- Does it survive?

```yaml
adversarial_test:
  - finding: "{achado}"
    lens: "GAP | INVERSION | EVASION"
    steel_man: "{melhor versao do argumento}"
    attack: "{contra-argumento mais forte}"
    counter_evidence: "{evidencia que contradiz}"
    verdict: "SURVIVES | WEAKENED | DESTROYED"
    action:
      survives: "Manter como achado confirmado"
      weakened: "Rebaixar confianca, marcar [NEEDS_VALIDATION]"
      destroyed: "Remover do output final"
```

**Questions by lens:**

| Lens | Steel Man | Attack |
|------|-----------|--------|
| GAP Analysis | "What if the gap is INTENTIONAL?" | "What if the gap is just disorganization?" |
| Inversions | "What is the strongest version?" | "What if it's EGO, not insight?" |
| Evasion Scan | "What is the most generous interpretation?" | "What if it's time limitation, not competence?" |

### Step 3: Clean Up Results

- DESTROYED findings: remove from output
- WEAKENED findings: mark with [NEEDS_VALIDATION]
- SURVIVES findings: confirm in final output

## Output

```yaml
cross_source_patterns: [{ confirmed patterns }]
adversarial_results: [{ per-finding verdicts }]
items_10_11:
  - item: 10
    status: "PASS|FAIL"
    confirmed_patterns: 0
  - item: 11
    status: "PASS|FAIL"
    survived: 0
    destroyed: 0
```

## Acceptance Criteria

- [ ] At least 1 pattern confirmed across 3+ independent sources
- [ ] At least 1 finding per lens passed adversarial test
- [ ] DESTROYED findings removed from output
- [ ] WEAKENED findings marked with [NEEDS_VALIDATION]

## Related Documents

| Document | Relationship |
|----------|-------------|
| `validate-extraction.md` | Parent orchestrator |
| `validate-extraction-checklist.md` | Previous phase |
| `validate-extraction-gate.md` | Next phase |
