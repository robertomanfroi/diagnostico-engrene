# Task: Generate and Register Workflow

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-workflow-generate` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-workflow-generate
name: Generate and Register Workflow
category: workflow-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Compile all workflow data into a complete YAML file using
  workflow-tmpl.yaml, run SC_WFL_001 quality gate, validate
  with workflow-validator.js, save the file, register in squad
  config.yaml, update README, and present handoff summary.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_workflow_generate
Output: artifact::create_workflow_generate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Assemble the complete workflow YAML file from all preceding task outputs, validate it through quality gates and contract checks, save it, and complete the pipeline by registering the workflow in the squad's configuration and documentation. No new decisions -- only structured generation, validation, registration, and reporting.

## Prerequisites

- [ ] Classification complete (create-workflow-classify output)
- [ ] Workflow design complete (create-workflow-design output, SC_PHS_001 + SC_AGN_001 + SC_CKP_001 passed)
- [ ] `templates/workflow-tmpl.yaml` is accessible

## Inputs

```yaml
inputs:
  - name: phase_0_classification
    type: object
    required: true
    source: previous_task
    description: "Classification from create-workflow-classify"

  - name: workflow_design
    type: object
    required: true
    source: previous_task
    description: "Complete design from create-workflow-design (phases, agents, task_refs, handoffs, gates, error_handling)"

  - name: squad_name
    type: string
    required: true
    source: previous_task
    description: "Target squad identifier"
```

## Workflow / Steps

### Step 1: Compile Workflow File

**Template:** `templates/workflow-tmpl.yaml`

```yaml
compile_workflow:
  sections:
    - header: "id, name, duration, description"
    - best_for: "Use cases from scope"
    - decision_matrix_fit: "When to use this workflow"
    - clone_combinations: "Agent combinations"
    - phases: "All phases with tasks and checkpoints"
    - error_handling: "Error procedures"
    - signals: "completion, checkpoint, blocked"
    - outputs: "All artifacts produced"
    - agents_by_phase: "Agent assignments"
    - quality_checklist: "Per-phase criteria"
    - metadata: "Version, created, author"

  output_location: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"
```

### Step 2: Run Quality Gate SC_WFL_001

```yaml
run_quality_gate:
  heuristic_id: SC_WFL_001
  name: "Workflow Quality Gate"
  blocking: true

  blocking_requirements:
    phases: ">= 3"
    each_phase_has:
      - id: true
      - name: true
      - days: true
      - tier: true
      - tasks: ">= 1"
      - checkpoint: true
    tier_0_exists: true
    agents_assigned: true
    error_handling: "defined"

  scoring:
    completeness: { weight: 0.25 }
    checkpoints: { weight: 0.20 }
    agents: { weight: 0.20 }
    inline_structures: { weight: 0.15 }
    error_handling: { weight: 0.10 }
    documentation: { weight: 0.10 }

  threshold: 7.0
  min_lines: 500
  min_phases: 3
```

### Step 3: Validate Workflow Contract

Run `workflow-validator.js` in strict mode (`--strict --fail-on-warnings`). Zero errors and zero warnings required. On failure: stop, fix, rerun.

### Step 4: Save Workflow File

```yaml
save_workflow:
  path: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"

  post_save:
    - verify_yaml_valid
    - log_creation
```

### Step 5: Update config.yaml

Add the workflow to the squad's configuration:

```yaml
update_config:
  file: "squads/{squad_name}/config.yaml"
  section: "workflows"
  add:
    - id: "wf-{workflow_id}"
      name: "{workflow_name}"
      file: "workflows/wf-{workflow_id}.yaml"
      phases: "{phase_count}"
      agents: "{agent_count}"
```

### Step 6: Update README

Add the workflow to the squad's README:

```yaml
update_readme:
  file: "squads/{squad_name}/README.md"
  section: "Workflows"
  add:
    entry: "- **{workflow_name}** (`wf-{workflow_id}.yaml`) -- {description}"
```

### Step 7: Present Handoff Summary

```yaml
present_summary:
  workflow_created:
    name: "{workflow_name}"
    id: "wf-{workflow_id}"
    file: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"
    lines: "{line_count}"

  structure:
    phases: "{phase_count}"
    total_tasks: "{task_count}"
    checkpoints: "{checkpoint_count}"
    agents_involved: "{agent_count}"

  quality:
    score: "{SC_WFL_001_score}/10"
    contract: "PASS"
    status: "PASS"

  next_actions:
    - "Review workflow file for domain accuracy"
    - "Create any placeholder tasks marked as TODO"
    - "Test workflow execution with a sample run"
```

## Output

```yaml
output:
  name: workflow_complete
  format: yaml
  structure:
    workflow_file:
      location: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"
      score: "{SC_WFL_001 score}/10"
      contract_validation: "PASS | FAIL"
      lines: "{line count}"
      status: "PASS | FAIL"
    registration:
      config_updated: true
      readme_updated: true
      summary_presented: true
```

## Acceptance Criteria

- [ ] Workflow file is valid YAML
- [ ] Uses workflow-tmpl.yaml structure
- [ ] SC_WFL_001 score >= 7.0
- [ ] All blocking requirements pass
- [ ] workflow-validator.js passes in --strict --fail-on-warnings
- [ ] File has >= 500 lines
- [ ] At least 1 inline structure (recommended)
- [ ] File saved to correct location
- [ ] Workflow added to config.yaml workflows section
- [ ] README updated with workflow entry
- [ ] Handoff summary presented with structure and quality metrics
- [ ] All file paths are correct and files exist

## Veto Conditions

- SC_WFL_001 score < 7.0
- workflow-validator.js reports errors
- Invalid YAML syntax
- Missing required sections from template
- config.yaml update fails or corrupts existing content
- Workflow file does not exist at expected path
- Registration attempted before validation passes

## Related Documents

- `templates/workflow-tmpl.yaml` -- Workflow file template
- `.aiox-core/development/scripts/workflow-validator.js` -- Contract validator
- `create-workflow-design.md` -- Preceding task (workflow design)
- `create-workflow.md` -- Parent composed task
- `squads/{squad_name}/config.yaml` -- Target configuration file
- `squads/{squad_name}/README.md` -- Target documentation file

---

_Task Version: 2.0.0_
_Merged from: create-workflow-generate.md (v1.0.0) + create-workflow-register.md (v1.0.0)_
