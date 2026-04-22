---
task-id: extract-sop-assemble
name: "Blueprint, Gap Analysis & Document Assembly"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
estimated-time: 25 min
complexity: medium

inputs:
  required:
    - task_anatomy_map: "From Phase 2"
    - decision_rules: "From Phase 2"
    - automation_analysis: "From Phase 3"
    - quality_score: "From Phase 3"

outputs:
  primary:
    - sop_document: "Complete SOP following SC-PE-001 template"
    - squad_blueprint: "Ready-to-use squad structure YAML"
    - gap_report: "Missing information and clarifying questions"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-sop-assemble
  task_name: Blueprint, Gap Analysis & Document Assembly
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 25m
  domain: Operational
  input:
  - '{''task_anatomy_map'': ''From Phase 2''}'
  - '{''decision_rules'': ''From Phase 2''}'
  - '{''automation_analysis'': ''From Phase 3''}'
  - '{''quality_score'': ''From Phase 3''}'
  output:
  - '{''sop_document'': ''Complete SOP following SC-PE-001 template''}'
  - '{''squad_blueprint'': ''Ready-to-use squad structure YAML''}'
  - '{''gap_report'': ''Missing information and clarifying questions''}'
  action_items:
  - Generate Squad Blueprint
  - Gap Analysis
  - Document Assembly
  - Error Handling Reference
  acceptance_criteria:
  - Squad blueprint generated with agents, tasks, guardrails
  - All gaps documented with clarifying questions
  - No [INFERRED] items left unvalidated
  - SOP document follows SC-PE-001 template (all 11 parts)
  - Mermaid diagrams generated
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


# Task: Blueprint, Gap Analysis & Document Assembly

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-sop-assemble` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-sop` (orchestrator stub)
- **Sequence:** Phase 4 of 4
- **Previous Task:** `extract-sop-analyze`
- **Next Task:** None (final phase)

## Purpose

Generate squad blueprint from extracted data, document all gaps and assumptions, and assemble the final SOP document using the SC-PE-001 template.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-ESP-002 | Existing SOP files must be backed up before overwrite | BLOCK |

## Workflow / Steps

### Step 1: Generate Squad Blueprint

Based on extracted data, generate:

1. **Agents needed** -- One per major responsibility
2. **Tasks to create** -- One per workflow phase
3. **Checkpoints** -- Where human validation required
4. **Guardrails** -- Required safeguards per task
5. **Workflow YAML** -- Orchestration definition

### Step 2: Gap Analysis

Document all:

1. **Missing information** -- What wasn't explained
2. **Ambiguities** -- Multiple interpretations possible
3. **Assumptions** -- What was inferred (mark [INFERRED])
4. **Red flags** -- Single points of failure, undocumented exceptions

**Output:** Gap report with clarifying questions

### Step 3: Document Assembly

Assemble final SOP using template `pop-extractor-prompt.md`:

1. Fill all 11 parts
2. Generate Mermaid diagrams
3. Complete all tables
4. Add glossary terms
5. Set metadata

### Step 4: Error Handling Reference

| Error | Cause | Resolution |
|-------|-------|------------|
| Incomplete transcript | Audio quality, speaker overlap | Request clarification |
| Conflicting information | Multiple speakers disagree | Document both, flag |
| Missing steps | Tacit knowledge not verbalized | Add to gaps |
| Unclear executor | Role not specified | Default to Hybrid, flag |

## Handoff

```yaml
handoff:
  to: "create-squad"
  trigger: "sop_validated = true"
  data_transferred:
    - sop_document
    - squad_blueprint
    - gap_report
  validation: "Process owner confirms accuracy"
```

## Output

```yaml
sop_document: "Complete SC-PE-001 SOP"
squad_blueprint: "YAML squad structure"
gap_report: "Gaps + clarifying questions"
```

## Acceptance Criteria

- [ ] Squad blueprint generated with agents, tasks, guardrails
- [ ] All gaps documented with clarifying questions
- [ ] No [INFERRED] items left unvalidated
- [ ] SOP document follows SC-PE-001 template (all 11 parts)
- [ ] Mermaid diagrams generated
- [ ] Handoff package ready for create-squad

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-sop.md` | Parent orchestrator |
| `extract-sop-analyze.md` | Previous phase |
| `create-squad.md` | Handoff target |
| `templates/pop-extractor-prompt.md` | SOP template |
