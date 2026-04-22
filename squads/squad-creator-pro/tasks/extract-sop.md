---
task: "Extract SOP from Transcript"
task_id: extract-sop
version: 2.0.0
execution_type: Orchestrator
model: Opus
model_rationale: "Orchestrator stub -- delegates to 4 atomic sub-tasks. Opus for semantic extraction."
haiku_eligible: false
note: "Decomposed from v1.1.0 monolith (340 lines, 9 steps) into 4 atomic tasks."
responsavel: "@squad-chief"
responsavel_type: agent
atomic_layer: task
estimated-time: 1-2 hours
complexity: medium

templates:
  - pop-extractor-prompt
config:
  - squad-config

inputs:
  required:
    - transcript: "Meeting transcript (text, audio transcription, or video transcript)"
  optional:
    - domain_context: "Business domain/area for terminology context"
    - existing_docs: "Current SOPs, manuals, or process docs"
    - process_owner: "Who to validate extracted SOP with"

outputs:
  primary:
    - sop_document: "Complete SOP following SC-PE-001 template"
    - squad_blueprint: "Ready-to-use squad structure"
    - gap_report: "Missing information and clarifying questions"
    - automation_analysis: "Summary of automation potential"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-sop
  task_name: Extract SOP from Transcript
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 1-2h
  domain: Operational
  input:
  - '{''transcript'': ''Meeting transcript (text, audio transcription, or video transcript)''}'
  - '{''domain_context'': ''Business domain/area for terminology context''}'
  - '{''existing_docs'': ''Current SOPs, manuals, or process docs''}'
  - '{''process_owner'': ''Who to validate extracted SOP with''}'
  output:
  - '{''sop_document'': ''Complete SOP following SC-PE-001 template''}'
  - '{''squad_blueprint'': ''Ready-to-use squad structure''}'
  - '{''gap_report'': ''Missing information and clarifying questions''}'
  - '{''automation_analysis'': ''Summary of automation potential''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - All 11 parts of SC-PE-001 completed
  - Task Anatomy (8 fields) for each step
  - Decision rules extracted as IF/THEN
  - Automation analysis completed (PV_PM_001)
  - META-AXIOMAS score >= 7.0
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


# Extract SOP from Transcript

**Squad:** squad-creator
**Phase:** Discovery
**Agent:** @squad-chief
**Pattern:** SC-PE-001 (SOP Extraction Standard)

---

## Pipeline (4 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `extract-sop-prepare` | Fetch Transcript & Preparation | 15 min |
| 2 | `extract-sop-extract` | 3-Pass Extraction (Structure, Anatomy, Decisions) | 30 min |
| 3 | `extract-sop-analyze` | Automation Analysis & Quality Assessment | 20 min |
| 4 | `extract-sop-assemble` | Blueprint, Gap Analysis & Document Assembly | 25 min |

---

## Execution Flow

```
extract-sop-prepare
  | transcript_object, preparation_notes
  v
extract-sop-extract
  | raw_steps, task_anatomy_map, decision_rules
  v
extract-sop-analyze
  | automation_analysis, quality_score (META-AXIOMAS >= 7.0)
  v
extract-sop-assemble
  | sop_document, squad_blueprint, gap_report (FINAL OUTPUT)
  v
[DONE → handoff to create-squad]
```

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-ESP-001 | Transcript must be non-empty | Validate transcript_content length > 0 | VETO - BLOCK |
| VETO-ESP-002 | Existing SOP files must be backed up before overwrite | Check if output files exist | VETO - BLOCK |
| VETO-ESP-003 | META-AXIOMAS score must be >= 7.0 | Verify quality assessment | VETO - BLOCK |

---

## Checklist Reference

Before marking complete, verify against: `checklists/sop-validation.md`

---

## Handoff

```yaml
handoff:
  to: "create-squad"
  trigger: "sop_validated = true"
  data_transferred:
    - sop_document
    - squad_blueprint
    - gap_report
```

---

## Validation

- [ ] All 11 parts of SC-PE-001 completed
- [ ] Task Anatomy (8 fields) for each step
- [ ] Decision rules extracted as IF/THEN
- [ ] Automation analysis completed (PV_PM_001)
- [ ] META-AXIOMAS score >= 7.0
- [ ] Squad blueprint generated
- [ ] Gaps documented with questions

---

**Pattern Compliance:** SC-PE-001 | HO-TP-001 | HO-TP-002

## Task Anatomy

- **Executor:** Agent
- **Inputs:** transcript
- **Outputs:** Complete SOP following SC-PE-001 template; Ready-to-use squad structure; Missing information and clarifying questions; Summary of automation potential
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Complete SOP following SC-PE-001 template
- [ ] Task output validated against quality standards
