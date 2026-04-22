---
task: "Extract Knowledge: Checklist Generation"
task_id: extract-knowledge-checklist
version: 1.0.0
execution_type: Agent
model: Sonnet
model_rationale: "Checklist generation is deterministic transformation from SOP -- no deep comprehension needed."
haiku_eligible: true
responsavel: "@tim-ferriss"
responsavel_type: agent
atomic_layer: task
elicit: false
phase: discovery
parent_task: extract-knowledge

workflows:
  - wf-extraction-pipeline
config:
  - squad-config
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-knowledge-checklist
  task_name: Checklist Generation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - '.1: Read Complete SOP'
  - '.2: Generate Step Checkboxes'
  - '.3: Generate Gate Checkboxes'
  - '.4: Validate 1:1 Correspondence'
  acceptance_criteria:
  - '[Precondition 1 from SOP]'
  - '[Precondition 2 from SOP]'
  - '[Action item 1 from SOP]'
  - '[Action item 2 from SOP]'
  - '[Output 1] produced'
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Checklist Generation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-knowledge-checklist` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |
| **Estimated Time** | `15-30 min` |

## Metadata

| Key | Value |
|-----|-------|
| Parent Task | `extract-knowledge` |
| Phase | 3 (Checklist Generation) |
| Gate | `CHECKLIST_QUALITY` |
| Depends On | Phase 2 (SOP Extraction) |
| Skip Condition | `format == 'framework' OR format == 'sop'` |

## Purpose

Generate a validation checklist with 1:1 correspondence to the SOP. Every checkbox maps to an SOP element. No "safety" additions -- zero invention.

## Prerequisites

- Phase 2 (SOP Extraction) completed
- `{topic}-sop.md` available and passed SOP_QUALITY gate

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| topic | string | Yes | Specific topic |
| sop_file | file | Yes | SOP output from Phase 2 |

## Workflow / Steps

### Step 3.1: Read Complete SOP

```yaml
action: "Load SOP from Phase 2"
input: "{topic}-sop.md"
extract:
  - all_steps
  - all_preconditions
  - all_outputs
  - all_guardrails
  - all_decision_rules
```

### Step 3.2: Generate Step Checkboxes

For each SOP step:

```markdown
### Step X: [Step Name]

**Preconditions:**
- [ ] [Precondition 1 from SOP]
- [ ] [Precondition 2 from SOP]

**Execution:**
- [ ] [Action item 1 from SOP]
- [ ] [Action item 2 from SOP]

**Output Validation:**
- [ ] [Output 1] produced
- [ ] [Output 1] meets [quality criteria from SOP]

**Guardrails:**
- [ ] [Guardrail 1] verified
- [ ] [Guardrail 2] verified
```

### Step 3.3: Generate Gate Checkboxes

For each quality gate in SOP:

```markdown
### Quality Gate: [Gate Name]

- [ ] [Criterion 1 from SOP]
- [ ] [Criterion 2 from SOP]
- [ ] [Criterion 3 from SOP]
- [ ] Minimum score achieved: [X/Y]

**Decision:**
- [ ] PASS -> Proceed to next phase
- [ ] FAIL -> Return to [step] for remediation
```

### Step 3.4: Validate 1:1 Correspondence

```yaml
validation:
  for_each_checkbox:
    - has_corresponding_sop_element: true
    - source_traceable: true
  for_each_sop_step:
    - has_checkbox_coverage: true
  invented_checkboxes: 0
```

### Checklist Quality Gate

| Criterion | Requirement | Status |
|-----------|-------------|--------|
| Step coverage | 100% of SOP steps | [ ] |
| Checkbox mapping | Each -> SOP element | [ ] |
| Zero invention | No "safety" additions | [ ] |
| Gates included | All quality gates | [ ] |
| Logical sequence | Matches SOP order | [ ] |

**Threshold:** 5/5 required

### Anti-Invention Check (Checklist)

- [ ] Every checkbox maps to SOP step?
- [ ] No "safety" checkboxes invented?
- [ ] Sequence reflects SOP faithfully?

## Output

| Output | Type | Location | Description |
|--------|------|----------|-------------|
| checklist | MD | `squads/{squad}/checklists/{topic}-sop-checklist.md` | Validation checklist |

## Acceptance Criteria

- [ ] 100% SOP step coverage in checkboxes [threshold: score >= 0.8]
- [ ] Each checkbox maps to a specific SOP element [threshold: score >= 0.8]
- [ ] All quality gates from SOP included as gate checkboxes [threshold: >= 1]
- [ ] Zero invented checkboxes (no "safety" additions) [threshold: >= 0]
- [ ] Logical sequence matches SOP order [threshold: score >= 0.8]
- [ ] CHECKLIST_QUALITY gate: 5/5 passed [threshold: >= 5]
- [ ] Anti-invention check: all items verified [threshold: score >= 0.8]
- [ ] `{topic}-sop-checklist.md` written to correct location [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EKN-003 | Zero-invention constraint | Validate every checkbox traces to SOP element | VETO - BLOCK. Remove invented checkboxes. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-knowledge.md` | Parent task (stub) |
| `extract-knowledge-sop.md` | Previous phase (dependency) |
| `extract-knowledge-validation.md` | Next phase (final validation) |
