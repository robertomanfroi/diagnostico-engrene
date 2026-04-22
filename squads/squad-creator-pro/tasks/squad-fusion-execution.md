<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-execution
  task_name: Squad Fusion -- Execution
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Prepare Rollback
  - Create Target Structure
  - Copy Unique Components
  - Merge Combined Components
  - Generate config.yaml
  acceptance_criteria:
  - Target directory created with complete structure
  - All keep-components copied without data loss
  - All merge-components combined preserving unique content
  - config.yaml is valid YAML with name, version, description
  - README.md has all 5 required sections
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
  Domain: Strategic
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Squad Fusion -- Execution

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-execution` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `worker` |

## Metadata

```yaml
id: squad-fusion-execution
name: "Squad Fusion Execution"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o merge plan: cria estrutura do target, copia componentes unicos, funde componentes combinados, gera config.yaml e README.md."
```

## Purpose

Executar o merge plan resolvido criando a estrutura do target squad, copiando componentes unicos, fundindo componentes combinados e gerando config.yaml e README.md. Unica fase que escreve no filesystem -- todas as anteriores sao read-only.

## Workflow / Steps

### Step 0: Prepare Rollback

Before any write operations, snapshot current state:

```yaml
prepare_rollback:
  actions:
    - record_git_state: "git rev-parse HEAD"
    - verify_clean_target: "squads/{target_name}/ must NOT exist"
    - log_rollback_procedure: "rollback-plan.yaml"
```

### Step 1: Create Target Structure

```yaml
create_target_structure:
  path: "squads/{target_name}/"
  structure:
    - agents/
    - tasks/
    - workflows/
    - templates/
    - checklists/
    - data/
    - scripts/
    - config/
    - docs/
```

### Step 2: Copy Unique Components

```yaml
copy_components:
  for_each: "{merge_plan.components_to_keep}"
  action: "Copy to target with resolved names"
  log: "copy_log.yaml"
  per_entry:
    - source_path: "{original}"
    - target_path: "{destination}"
    - status: "copied | skipped | error"
```

### Step 3: Merge Combined Components

```yaml
merge_components:
  for_each: "{merge_plan.components_to_merge}"
  action: "Merge content intelligently"
  preserve:
    - "All output_examples"
    - "All objection_algorithms"
    - "Unique vocabulary items"
    - "All acceptance criteria"
  log: "merge_log.yaml"
  per_entry:
    - sources: ["{path_a}", "{path_b}"]
    - target_path: "{merged_destination}"
    - merge_strategy: "{strategy used}"
    - status: "merged | error"
```

### Step 4: Generate config.yaml

```yaml
generate_config:
  template: "config-tmpl.yaml"
  values:
    name: "{target_name}"
    version: "1.0.0"
    description: "Fusao de {sources.join(', ')}"
    components: "{merged_components_summary}"
    agents: "{list of final agents}"
    capabilities: "{union of all capabilities}"
```

### Step 5: Generate README.md

```yaml
generate_readme:
  template: "readme-tmpl.md"
  sections:
    - "Overview (generated from config)"
    - "Merged from (source squads list)"
    - "Component inventory (counts by type)"
    - "Usage (activation commands)"
    - "Changelog (fusion event)"
```

### Step 6: Generate FUSION-LOG.md

```yaml
generate_fusion_log:
  contents:
    - fusion_date: "{timestamp}"
    - sources: "{list}"
    - target: "{target_name}"
    - mode: "{yolo | quality}"
    - components_copied: N
    - components_merged: N
    - components_discarded: N
    - conflicts_resolved: N
    - gaps_filled: N
    - resolution_details: "{from resolution-log.yaml}"
```

### Step 7: Checkpoint

```yaml
checkpoint:
  type: automatic
  validate:
    - "Target directory created with all subdirectories"
    - "All components copied or merged per plan"
    - "config.yaml valid YAML with required fields"
    - "README.md generated with all sections"
    - "FUSION-LOG.md complete"
    - "copy_log.yaml has zero errors"
    - "merge_log.yaml has zero errors"
  on_fail: "ROLLBACK and report"
```

## Rollback Procedure

If any step fails:

```yaml
rollback:
  trigger: "Any checkpoint validation fails OR user cancels"
  actions:
    - step_1: "Delete target directory: rm -rf squads/{target_name}/"
    - step_2: "Restore source squads if modified: git checkout -- squads/{sources}/"
    - step_3: "Log rollback reason to fusion-rollback-{timestamp}.log"
    - step_4: "Notify user with reason and next steps"
```

## Output

```yaml
output:
  schema:
    squad_path: "squads/{target_name}/"
    copy_log: "copy_log.yaml"
    merge_log: "merge_log.yaml"
    fusion_log: "FUSION-LOG.md"
```

## Acceptance Criteria

- [ ] Target directory created with complete structure
- [ ] All keep-components copied without data loss
- [ ] All merge-components combined preserving unique content
- [ ] config.yaml is valid YAML with name, version, description
- [ ] README.md has all 5 required sections
- [ ] FUSION-LOG.md records complete fusion history
- [ ] Zero errors in copy_log and merge_log
- [ ] Rollback procedure tested (target can be cleanly removed)

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-SFU-003 | Rollback path not prepared before write operations | BLOCK. Prepare rollback first. |

## Related Documents

- `squad-fusion.md` -- Parent stub task
- `squad-fusion-resolution.md` -- Previous phase (Phase 3)
- `squad-fusion-validation.md` -- Next phase (Phase 5)
