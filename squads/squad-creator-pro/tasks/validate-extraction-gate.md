---
task-id: validate-extraction-gate
name: "Gate Decision & Handoff/Loop"
version: 1.0.0
execution_type: Worker
model: Haiku
model_rationale: "Binary gate decision based on checklist scores. Deterministic."
haiku_eligible: true
estimated-time: 5 min
complexity: low

inputs:
  required:
    - checklist_results: "9 items from Phase 1"
    - adversarial_results: "Items 10-11 from Phase 2"
    - expert_name: "Nome do expert"

outputs:
  primary:
    - validation_report: "Complete report with gate decision"
    - gate_decision: "PASS or FAIL"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-extraction-gate
  task_name: Gate Decision & Handoff/Loop
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 5m
  domain: Operational
  input:
  - '{''checklist_results'': ''9 items from Phase 1''}'
  - '{''adversarial_results'': ''Items 10-11 from Phase 2''}'
  - '{''expert_name'': ''Nome do expert''}'
  output:
  - '{''validation_report'': ''Complete report with gate decision''}'
  - '{''gate_decision'': ''PASS or FAIL''}'
  action_items:
  - Consolidate All 11 Items
  - Apply Gate Decision
  - Generate Validation Report
  - 'a: If FAIL -- Identify Gaps'
  - 'b: If PASS -- Prepare Handoff Package'
  acceptance_criteria:
  - All 11 items consolidated with status
  - Gate decision is deterministic (all PASS = PASS, any FAIL = FAIL)
  - 'If FAIL: gaps identified with corrective action'
  - 'If PASS: handoff package listed and ready'
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Gate Decision & Handoff/Loop

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-extraction-gate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

- **Parent Task:** `validate-extraction` (orchestrator stub)
- **Sequence:** Phase 3 of 3
- **Previous Task:** `validate-extraction-adversarial`
- **Next Task:** None (final phase)

## Purpose

Consolidar os 11 itens do checklist, determinar PASS ou FAIL, e produzir o relatorio de validacao com pacote de handoff ou plano de correcao.

## Workflow / Steps

### Step 1: Consolidate All 11 Items

Merge checklist_results (items 1-9) with adversarial_results (items 10-11).

### Step 2: Apply Gate Decision

```
IF all 11 items PASS:
  gate_decision = PASS
  action = HANDOFF to @pedro-valerio
ELSE:
  gate_decision = FAIL
  action = LOOP (identify gaps, correct, re-validate)
```

### Step 3: Generate Validation Report

```yaml
validation_report:
  expert: "{expert_name}"
  checklist_results:
    - item: 1
      criterio: "Citacoes [SOURCE:]"
      result: "PASS|FAIL"
      count_evidence: "{numero}"
    # ... items 2-11
  gate_decision: "PASS | FAIL"
  items_passed: 0
  items_failed: 0
```

### Step 4a: If FAIL -- Identify Gaps

```yaml
fail_action:
  gaps_identified:
    - item: 0
      gap: "{what's missing}"
      action: "{how to fix}"
  next_action: "LOOP to correct gaps"
```

### Step 4b: If PASS -- Prepare Handoff Package

```yaml
handoff_package:
  artefatos_prontos:
    - "{expert}_dna.yaml"
    - "frameworks/*.md"
    - "heuristics.yaml"
    - "source-index.yaml"
  destination: "@pedro-valerio"
```

## Output

```yaml
validation_report: { complete report }
gate_decision: "PASS|FAIL"
handoff_package: { if PASS }
fail_action: { if FAIL }
```

## Acceptance Criteria

- [ ] All 11 items consolidated with status
- [ ] Gate decision is deterministic (all PASS = PASS, any FAIL = FAIL)
- [ ] If FAIL: gaps identified with corrective action
- [ ] If PASS: handoff package listed and ready

## Related Documents

| Document | Relationship |
|----------|-------------|
| `validate-extraction.md` | Parent orchestrator |
| `validate-extraction-adversarial.md` | Previous phase |
