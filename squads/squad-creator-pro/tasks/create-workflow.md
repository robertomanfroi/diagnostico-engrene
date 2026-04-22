<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-workflow
  task_name: Create Squad Workflow (Extension Wrapper)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  action_items:
    - Normalize Target Squad
    - Build Base Payload
    - Delegate to Base Workflow
    - Reconcile Outputs for Pro Callers
  acceptance_criteria:
    - "squads/squad-creator/workflows/wf-create-workflow.yaml existe"
    - "pack_name e squad_name são reconciliados corretamente"
    - "o wrapper não define pipeline próprio"
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

# Task: Create Squad Workflow (Extension Wrapper)

**Task ID:** create-workflow  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` delegando a criação real de workflows ao pipeline atômico do `squad-creator`

## Canonical Owner

- `squads/squad-creator/workflows/wf-create-workflow.yaml`
- `squads/squad-creator/tasks/create-workflow-{classify,design,generate}.md`

## Inputs

- `workflow_purpose` e `squad_name` são obrigatórios
- `workflow_name`, `workflow_id`, `duration` e `phase_count` refinam o payload
- `pack_name`, `source_artifacts` e `integration_notes` servem só para compatibilidade/enriquecimento

## Preconditions

- [ ] `squads/squad-creator/workflows/wf-create-workflow.yaml` existe
- [ ] o alvo resolve para `squads/{squad_name}/`
- [ ] o chamador entende que este wrapper não possui pipeline próprio

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

build_base_payload:
  required_fields: [workflow_purpose, squad_name]
  optional_fields:
    - workflow_name
    - workflow_id
    - duration
    - phase_count
    - source_artifacts
    - integration_notes

delegate_to_base:
  workflow: "squads/squad-creator/workflows/wf-create-workflow.yaml"
  contract:
    - use_base_classification
    - use_base_phase_design
    - use_base_task_binding
    - use_base_generation
    - use_base_registration
  prohibition:
    - "Do NOT recreate create-workflow-* atomics inside squad-creator-pro"
    - "Do NOT fork gates or state rules locally"

reconcile_outputs:
  workflow_file: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"
  delegated_workflow: "squads/squad-creator/workflows/wf-create-workflow.yaml"
  execution_mode: "base-delegated"
```

## Output

```yaml
output:
  workflow_file: "squads/{squad_name}/workflows/wf-{workflow_id}.yaml"
  delegated_workflow: "squads/squad-creator/workflows/wf-create-workflow.yaml"
  normalized_squad_name: "{squad_name}"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] a criação real do workflow é delegada ao workflow base
- [ ] nenhuma implementação paralela de create-workflow permanece no pro
- [ ] chamadores do pro continuam compatíveis

## Veto Conditions

- `squad_name` e `pack_name` apontam para squads diferentes
- `wf-create-workflow.yaml` não existe no base
- algum chamador exige fase inventada fora do base

## Related Documents

- `squads/squad-creator/workflows/wf-create-workflow.yaml`
- `squads/squad-creator/tasks/create-workflow.md`
- `workflows/wf-context-aware-create-squad.yaml`
- `workflows/wf-create-squad.yaml`
