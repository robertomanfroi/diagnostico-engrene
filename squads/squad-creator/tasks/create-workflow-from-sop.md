# Task: Create Workflow from SOP

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-workflow-from-sop` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata
```yaml
id: create-workflow-from-sop
name: "Create Workflow from SOP"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Transform a canonical SOP (human-readable .md or machine-readable .ml.yaml) into an executable YAML workflow following the workflow-tmpl.yaml schema. Extracts phases, steps, quality gates, and RACI to produce a valid workflow with auto-QA via analyze-workflow."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_workflow_from_sop
Output: artifact::create_workflow_from_sop
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Convert an existing Standard Operating Procedure (SOP) into an executable AIOX workflow YAML file. SOPs define **what** must happen in a process; workflows define **how** agents execute it. This task bridges that gap by:

1. Extracting the process structure from the SOP
2. Mapping it to the AIOX workflow schema
3. Assigning agents based on RACI roles
4. Creating checkpoints from quality gates
5. Auto-validating the result with `analyze-workflow`

This enables the SOP Factory's documented processes to become executable orchestrations in any squad.

## Prerequisites

- [ ] SOP file exists and is readable (.md or .ml.yaml format)
- [ ] Target squad exists (the squad where the workflow will be created)
- [ ] `workflow-tmpl.yaml` accessible for schema reference
- [ ] `analyze-workflow.md` task accessible for auto-QA

## Inputs

```yaml
inputs:
  sop_file:
    type: filepath
    required: true
    description: "Path to the SOP file (.md human-readable or .ml.yaml machine-readable)"

  target_squad:
    type: string
    required: true
    description: "Squad name where the workflow will be created (e.g., 'aiox-design')"

  workflow_name:
    type: string
    required: false
    description: "Override workflow name. If not provided, derived from SOP title."

  auto_qa:
    type: boolean
    required: false
    default: true
    description: "If true, automatically run analyze-workflow on the generated output"
```

## Elicitation Points

```yaml
elicitation:
  - point: "agent_mapping"
    question: "The SOP defines these roles: {roles_found}. How should they map to squad agents?"
    when: "SOP has RACI roles that don't map 1:1 to existing squad agents"
    options:
      - "Map manually (I'll specify agent per role)"
      - "Auto-map by role name similarity"
      - "Create placeholder agents for unmapped roles"

  - point: "checkpoint_level"
    question: "The SOP has {gate_count} quality gates. What checkpoint level for the workflow?"
    when: "always"
    options:
      - "All gates as human_review: true checkpoints"
      - "Critical gates as human, others as heuristic"
      - "All gates as heuristic (fully autonomous)"
```

## Workflow / Steps

### 1. Ingest SOP

```
ACTION: Read and parse the SOP file

DETECT FORMAT:
  - .md file → Human-readable SOP
    - Extract: Title, Purpose, Scope, Procedure steps, Quality Control,
      Error Handling, Responsibilities/RACI, References
  - .ml.yaml file → Machine-readable SOP
    - Extract: sop.id, sop.phases[], sop.quality_gates[],
      sop.raci{}, sop.inputs[], sop.outputs[]

EXTRACT (regardless of format):
  - sop_id: Unique identifier
  - sop_title: Display name
  - sop_version: Current version
  - phases[]: Logical process phases/stages
  - steps_per_phase[]: Individual steps within each phase
  - quality_gates[]: Quality control checkpoints
  - raci: { role: [R|A|C|I] } per step/phase
  - inputs: What the process needs to start
  - outputs: What the process produces
  - error_handling: Exception/escalation procedures
  - scope: What is in/out of scope

ON FAIL: STOP — "Cannot parse SOP file. Expected .md or .ml.yaml format."
```

### 2. Map Phases to Workflow Structure

```
ACTION: Transform SOP phases into workflow phases

FOR EACH sop_phase:
  CREATE workflow_phase:
    - id: "PHASE-{N}"
    - name: "{sop_phase.name}"
    - description: "{sop_phase.description}"
    - tier: Assign based on phase position (0=foundation, 1=core, 2=advanced, 3=polish)
    - days: Estimate from SOP time references or default "1-2"

  FOR EACH step IN sop_phase:
    - Map to task reference if existing task in target squad matches
    - Otherwise create task_description inline
    - Record outputs per step

RESULT: phases[] ready for workflow YAML
```

### 3. Assign Agents from RACI

```
ACTION: Map SOP roles to squad agents

STEPS:
  1. Read target squad config: squads/{target_squad}/config.yaml
  2. List available agents in the squad
  3. For each RACI role in the SOP:
     a. Match by role name similarity to agent IDs
     b. Match by role description to agent whenToUse
     c. If no match → ELICIT agent_mapping from user

MAPPING RULES:
  - R (Responsible) → phase.agent (primary executor)
  - A (Accountable) → phase checkpoint.reviewer or orchestrator
  - C (Consulted) → agents_by_phase.secondary
  - I (Informed) → handoff_prompts.context recipients

RESULT: Each phase has agent assignment
```

### 4. Create Checkpoints from Quality Gates

```
ACTION: Transform SOP quality gates into workflow checkpoints

FOR EACH quality_gate IN sop:
  CREATE checkpoint:
    - phase: Map to corresponding workflow phase
    - criteria: Extract measurable criteria from gate
    - human_review: Based on elicitation (checkpoint_level)
    - veto_condition: Derive from gate's failure consequences

QUALITY GATE MAPPING:
  - SOP "Verification" → checkpoint with criteria
  - SOP "Approval" → checkpoint with human_review: true
  - SOP "Sign-off" → checkpoint with veto_condition
  - SOP "Quality Control" → checkpoint with measurable thresholds

RESULT: Checkpoints integrated into phases
```

### 5. Generate Workflow YAML

```
ACTION: Assemble the complete workflow YAML using workflow-tmpl.yaml schema

SECTIONS TO POPULATE:
  1. Header: id, name, version, orchestrator, description, best_for
  2. sequence[]: Canonical executable contract (step, id, phase, agent, task, outputs, checkpoint)
  3. handoff_prompts: For each agent transition
  4. phases[]: Supplemental metadata
  5. error_handling: From SOP error handling section
  6. completion_signals: From SOP success criteria
  7. outputs: From SOP outputs section
  8. agents_by_phase: From RACI mapping
  9. quality_checklist: From quality gates
  10. metadata: version, framework, created date, source SOP reference

NAMING:
  - workflow_id: "wf-{sop-derived-name}" (e.g., "wf-a11y-audit" from SOP-DEV-A11Y-AUDIT)
  - filename: "workflows/wf-{sop-derived-name}.yaml"

WRITE: squads/{target_squad}/workflows/{filename}
```

### 6. Auto-QA via analyze-workflow

```
CONDITION: auto_qa = true (default)

ACTION: Run the generated workflow through analyze-workflow for quality validation

STEPS:
  1. Invoke analyze-workflow task with:
     - workflow_file: "{generated_workflow_path}"
     - scoring_mode: quick
  2. Review gap report results:
     - If score >= 70: PASS — workflow is acceptable
     - If score 50-69: WARN — document gaps, suggest user review
     - If score < 50: Apply top 3 P1 fixes automatically, re-validate

OUTPUT: QA results included in task completion summary

NOTE: This creates a feedback loop — SOP → Workflow → Analysis → Improvement
```

## Output

```yaml
outputs:
  primary:
    path: "squads/{target_squad}/workflows/wf-{sop-derived-name}.yaml"
    format: yaml
    description: "Complete workflow YAML derived from SOP"

  secondary:
    path: "outputs/aiox-sop/workflow-analysis/{workflow-name}-gap-report.yaml"
    format: yaml
    description: "Auto-QA gap report (if auto_qa=true)"
    condition: "auto_qa = true"

  metadata:
    source_sop: "{sop_file path}"
    source_sop_version: "{version}"
    workflow_id: "wf-{name}"
    target_squad: "{target_squad}"
    phases_created: "<number>"
    agents_mapped: "<number>"
    checkpoints_created: "<number>"
    auto_qa_score: "<0-100 or N/A>"
```

## Acceptance Criteria

- [ ] SOP file is successfully parsed (both .md and .ml.yaml supported)
- [ ] All SOP phases are mapped to workflow phases
- [ ] Agents are assigned to every phase (from RACI or user input)
- [ ] Checkpoints are created from quality gates
- [ ] Generated workflow is valid YAML
- [ ] Generated workflow follows workflow-tmpl.yaml schema
- [ ] workflow.sequence[] is present as canonical executable contract
- [ ] Error handling section is populated from SOP
- [ ] Metadata includes reference to source SOP
- [ ] Auto-QA runs and score is reported (if auto_qa=true)
- [ ] Workflow file written to target squad's workflows/ directory

## Veto Conditions

- STOP if the input file is not an SOP (must have SOP structure: Purpose, Procedure, etc.)
- STOP if the target squad does not exist
- STOP if the target squad has no agents defined (cannot assign workflow phases)
- `VETO-CWS-001`: STOP if the SOP has no identifiable procedure/process steps. A workflow cannot be created from a policy or reference document — it requires actionable steps.
- `VETO-CWS-002`: STOP if generated workflow YAML is invalid. Fix syntax before writing.
- `VETO-CWS-003`: STOP if auto-QA returns score < 50 after one round of self-fixes. Escalate to user for manual review.

## Related Documents

- `analyze-workflow.md` — Used for auto-QA of generated workflow (aiox-sop)
- `workflow-tmpl.yaml` — Canonical workflow schema
- `workflow-yaml-schema.yaml` — YAML schema for validation
- `create-workflow.md` — General workflow creation task (this task is SOP-specific)
- `sop-workflow-integration.md` — Integration protocol between squads
