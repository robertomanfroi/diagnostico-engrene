<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: migrate-workflows-analyze
  task_name: Migrate Workflows -- Analyze
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Read and Map Structure
  - Generate Structure Map
  acceptance_criteria:
  - Read each legacy .md workflow and map structure
  - Read `workflow-tmpl.yaml` template for target format
  - Identify gaps between source .md and target YAML template
  - All .md workflow files read and structure extracted
  - Template YAML format understood
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Migrate Workflows -- Analyze

**Task ID:** migrate-workflows-analyze
**Parent Task:** `migrate-workflows-to-yaml.md`
**Purpose:** Read legacy .md workflow files, extract structure, identify gaps vs YAML template
**Execution Type:** Hybrid
**Model:** `Sonnet`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Migrate Workflows -- Analyze |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | .md workflow files + `workflow-tmpl.yaml` template |
| **output** | Structure map per workflow |
| **action_items** | 2 steps |
| **acceptance_criteria** | All .md files analyzed, gaps identified |

---

## Workflow

### Step 1: Read and Map Structure

For each .md workflow file, extract:

- workflow-id
- name/purpose
- version
- phases (main sections)
- inputs/outputs
- checkpoints
- frameworks used
- agents involved

**Substeps:**

- [ ] Read each legacy .md workflow and map structure
- [ ] Read `workflow-tmpl.yaml` template for target format
- [ ] Identify gaps between source .md and target YAML template

### Step 2: Generate Structure Map

```yaml
workflow_analysis:
  - source_file: "{path}"
    extracted:
      workflow_id: "{id}"
      name: "{name}"
      version: "{version}"
      phases_count: {n}
      phases: []
      inputs: []
      outputs: []
      agents: []
      frameworks: []
    gaps:
      - field: "{missing field}"
        severity: "required|optional"
        resolution: "extract from context | ask user"
```

---

## Output Contract

```yaml
migration_analysis:
  template_used: "workflow-tmpl.yaml"
  workflows_analyzed: {n}
  workflows:
    - source: "{path}"
      structure: {extracted fields}
      gaps: [{gap list}]
      ready_for_conversion: true|false
```

---

## Completion Criteria

- [ ] All .md workflow files read and structure extracted
- [ ] Template YAML format understood
- [ ] Gaps between source and target identified per file
- [ ] Structure map generated

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `migrate-workflows-convert.md` |
| **Trigger** | Analysis complete |
| **Artifact** | `migration_analysis` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of migrate-workflows-to-yaml.md_

## Acceptance Criteria

- [ ] All .md files analyzed
- [ ] gaps identified
