<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: qualify-task
  task_name: qualify-task
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Validate Qualification Request
  - Delegate to Canonical Workflow
  - Reconcile Outputs
  acceptance_criteria:
  - '`wf-model-tier-qualification.yaml` existe e permanece owner canônico'
  - single mode e batch mode continuam suportados pelo entrypoint legado
  - '`test_input_registry` permanece como fonte única da elegibilidade'
  - nenhuma segunda implementação local de comparação de modelos permanece nesta task
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: qualify-task

**Task ID:** qualify-task  
**Version:** 3.1.0  
**Purpose:** manter o entrypoint `*qualify-task` como contrato curto enquanto `wf-model-tier-qualification.yaml` possui a lógica empírica completa

## Canonical Workflow

- `squads/squad-creator-pro/workflows/wf-model-tier-qualification.yaml`

## Inputs

- `task_name` é obrigatório no modo single
- `target_tier` e `threshold` refinam a execução
- `force`, `batch` e `wave` controlam reexecução e escopo do lote

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-model-tier-qualification.yaml` existe
- [ ] `task_name` resolve para `test_input_registry.{task_name}` no workflow, exceto em modo batch
- [ ] o chamador entende que a decisão final de tier é produzida pelo workflow, não por lógica local desta task

## Execution Contract

```yaml
validate_request:
  single_mode:
    task_path: "squads/squad-creator-pro/tasks/{task_name}.md"
    registry_lookup: "wf-model-tier-qualification.yaml:test_input_registry.{task_name}"
    routing_guard: "config/model-routing.yaml → tasks.{task_name}.validated"
  batch_mode:
    execution_order: "wf-model-tier-qualification.yaml:batch_mode.execution_order"
    filter: "tasks ainda não validadas, salvo --force"

delegate_to_workflow:
  workflow: "squads/squad-creator-pro/workflows/wf-model-tier-qualification.yaml"
  payload:
    - task_name
    - target_tier
    - threshold
    - force
    - batch
    - wave
  workflow_owns:
    - pre-flight
    - opus_vs_candidate_execution
    - compare_auto_decide
    - compensation_loop
    - report_generation

reconcile_outputs:
  report: "test-cases/{task_name}/qualification-report.yaml"
  dashboard: "squads/squad-creator-pro/test-cases/QUALIFICATION-DASHBOARD.yaml"
  routing_update: "config/model-routing.yaml"
  status: "delegated"
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-model-tier-qualification.yaml"
  primary_report: "test-cases/{task_name}/qualification-report.yaml"
  batch_dashboard: "squads/squad-creator-pro/test-cases/QUALIFICATION-DASHBOARD.yaml"
  routing_update_target: "config/model-routing.yaml"
  status: "delegated"
```

## Acceptance Criteria

- [ ] o workflow canônico executa a qualificação empírica completa
- [ ] single mode e batch mode continuam suportados pelo entrypoint legado
- [ ] `test_input_registry` permanece como fonte única da elegibilidade
- [ ] nenhuma segunda implementação local de comparação de modelos permanece nesta task
