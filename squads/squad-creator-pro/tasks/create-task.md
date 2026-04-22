<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-task
  task_name: Create Squad Task (Extension Wrapper)
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
    - "squads/squad-creator/workflows/wf-create-task.yaml existe"
    - "pack_name e squad_name são reconciliados corretamente"
    - "o wrapper não define pipeline paralelo"
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

# Task: Create Squad Task (Extension Wrapper)

**Task ID:** create-task  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` delegando a criação real de tasks ao pipeline atômico do `squad-creator`

## Canonical Owner

- `squads/squad-creator/workflows/wf-create-task.yaml`
- `squads/squad-creator/tasks/create-task-{classify,anatomy,executor,generate,validate,register}.md`

## Inputs

- `task_purpose` e `task_name` são obrigatórios
- `squad_name` é preferido; `pack_name` é aceito como alias legado
- `source_framework`, `source_artifacts` e `integration_notes` apenas enriquecem a delegação

## Preconditions

- [ ] `squads/squad-creator/workflows/wf-create-task.yaml` existe
- [ ] o alvo resolve para `squads/{squad_name}/`
- [ ] o chamador entende que o wrapper não possui pipeline próprio

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

build_base_payload:
  required_fields: [task_purpose, task_name, squad_name]
  optional_context: [source_framework, source_artifacts, integration_notes]

delegate_to_base:
  workflow: "squads/squad-creator/workflows/wf-create-task.yaml"
  contract:
    - use_base_classification
    - use_base_anatomy
    - use_base_executor_design
    - use_base_generation
    - use_base_validation
    - use_base_registration
  prohibition:
    - "Do NOT recreate create-task-* atomics inside squad-creator-pro"
    - "Do NOT fork quality gates locally"

reconcile_outputs:
  task_file: "squads/{squad_name}/tasks/{task_id}.md"
  delegated_workflow: "squads/squad-creator/workflows/wf-create-task.yaml"
  execution_mode: "base-delegated"
```

## Output

```yaml
output:
  task_file: "squads/{squad_name}/tasks/{task_id}.md"
  delegated_workflow: "squads/squad-creator/workflows/wf-create-task.yaml"
  normalized_squad_name: "{squad_name}"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] a criação real da task é delegada ao workflow base
- [ ] nenhuma fase paralela de create-task existe no pro
- [ ] chamadores do pro continuam compatíveis

## Veto Conditions

- `squad_name` e `pack_name` apontam para squads diferentes
- `wf-create-task.yaml` não existe no base
- algum chamador exige fase inventada fora do base

## Related Documents

- `squads/squad-creator/workflows/wf-create-task.yaml`
- `squads/squad-creator/tasks/create-task.md`
- `workflows/wf-context-aware-create-squad.yaml`
- `workflows/wf-research-then-create-agent.yaml`
