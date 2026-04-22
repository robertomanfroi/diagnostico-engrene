---
task-id: an-extract-framework
name: "Extract Framework (Trinity)"
version: 2.0.0
execution_type: Orchestrator
model: Opus
model_rationale: "Orchestrator stub -- delegates to 3 atomic sub-tasks. Opus for deep semantic extraction."
haiku_eligible: false
note: "Decomposed from v1.0.0 monolith (338 lines, 5 steps) into 3 atomic tasks."
estimated-time: 30-60 min
complexity: medium

inputs:
  required:
    - source: "Source material (interview, book, course, post, video)"

outputs:
  primary:
    - playbook: "Step-by-step methodology"
    - framework: "SE/ENTAO decision rules"
    - swipe_file: "Real examples and cases"
    - cross_lens_map: "Integrated territory map"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-framework
  task_name: Extract Framework (Trinity)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 30-60m
  domain: Operational
  input:
  - '{''source'': ''Source material (interview, book, course, post, video)''}'
  output:
  - '{''playbook'': ''Step-by-step methodology''}'
  - '{''framework'': ''SE/ENTAO decision rules''}'
  - '{''swipe_file'': ''Real examples and cases''}'
  - '{''cross_lens_map'': ''Integrated territory map''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - GAP Analysis executado (prometido vs entregue + adversarial test)
  - Playbook extraido (passo a passo)
  - Framework extraido (regras SE/ENTAO)
  - Swipe File extraido (exemplos validados)
  - Paradigm Inversions extraidas (>= 1 + adversarial test)
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


# Extract Framework (Trinity)

**Command:** `*extract-framework {source}`

> **Trindade:** Playbook (O QUE) + Framework (QUANDO/POR QUE) + Swipe File (COMO)

---

## Checklist Reference

Before marking complete, verify against: `checklists/mental-model-integration-checklist.md`

---

## Pipeline (3 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `an-extract-framework-analyze` | Source Classification & GAP Analysis | 10 min |
| 2 | `an-extract-framework-trinity` | Extract Playbook, Framework & Swipe File | 30 min |
| 3 | `an-extract-framework-integrate` | Paradigm Inversions & Cross-Lens Integration | 15 min |

---

## Execution Flow

```
an-extract-framework-analyze
  | source_quality, gap_analysis
  v
an-extract-framework-trinity
  | playbook, framework, swipe_file
  v
an-extract-framework-integrate
  | paradigm_inversions, cross_lens_map (FINAL OUTPUT)
  v
[DONE]
```

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-AEF-001 | Source quality must be classified before extraction | Verify OURO/BRONZE classification | VETO - BLOCK |
| VETO-AEF-002 | Existing Trinity artifacts must be backed up | Check if target files exist | VETO - BLOCK |
| VETO-AEF-003 | Output must include all three legs with evidence | Verify Playbook + Framework + Swipe File with [SOURCE:] | VETO - BLOCK |

---

## Completion Criteria

- [ ] GAP Analysis executado (prometido vs entregue + adversarial test)
- [ ] Playbook extraido (passo a passo)
- [ ] Framework extraido (regras SE/ENTAO)
- [ ] Swipe File extraido (exemplos validados)
- [ ] Paradigm Inversions extraidas (>= 1 + adversarial test)
- [ ] Cross-Lens Integration Map gerado
- [ ] Completude validada (3 pernas + lentes integradas)

## Task Anatomy

- **Executor:** Agent
- **Inputs:** source
- **Outputs:** Step-by-step methodology; SE/ENTAO decision rules; Real examples and cases; Integrated territory map
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Step-by-step methodology
- [ ] Task output validated against quality standards
