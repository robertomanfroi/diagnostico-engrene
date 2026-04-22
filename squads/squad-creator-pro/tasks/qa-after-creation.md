<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: qa-after-creation
  task_name: QA After Creation (Extension Wrapper)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Build Base QA Payload
  - Delegate to Base Workflow
  - Reconcile Outputs
  acceptance_criteria:
  - '`squads/squad-creator/workflows/wf-qa-after-creation.yaml` existe'
  - O QA real é delegado ao workflow base
  - chamadas existentes do pro continuam compatíveis
  - nenhuma implementação paralela de QA-after-creation permanece no pro
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
  Domain: Operational
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: QA After Creation (Extension Wrapper)

**Task ID:** qa-after-creation  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` enquanto delega o QA pós-criação ao pipeline canônico do `squad-creator`

## Canonical Owner

- `squads/squad-creator/workflows/wf-qa-after-creation.yaml`
- `squads/squad-creator/tasks/qa-after-creation.md`

## Inputs

- `created_component` e `component_type` são obrigatórios
- `creation_task`, `auto_fix` e `specialist_context` apenas enriquecem o payload

## Preconditions

- [ ] `squads/squad-creator/workflows/wf-qa-after-creation.yaml` existe
- [ ] o componente alvo existe no path informado
- [ ] o chamador entende que este wrapper não mantém pipeline próprio

## Execution Contract

```yaml
build_base_payload:
  required:
    - created_component
    - component_type
  optional:
    - creation_task
    - auto_fix
    - specialist_context
  rule: "o contexto do pro pode enriquecer o relatório, mas não cria uma segunda implementação"

delegate_to_base:
  workflow: "squads/squad-creator/workflows/wf-qa-after-creation.yaml"
  payload:
    - created_component
    - component_type
    - creation_task
    - auto_fix
    - specialist_context
  prohibition:
    - "Do NOT maintain a parallel QA-after-creation pipeline in squad-creator-pro"

reconcile_outputs:
  delegated_workflow: "squads/squad-creator/workflows/wf-qa-after-creation.yaml"
  execution_mode: "base-delegated"
  created_component: "{created_component}"
  component_type: "{component_type}"
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator/workflows/wf-qa-after-creation.yaml"
  created_component: "{created_component}"
  component_type: "{component_type}"
  status: "delegated"
```

## Acceptance Criteria

- [ ] o QA real é delegado ao workflow base
- [ ] chamadas existentes do pro continuam compatíveis
- [ ] nenhuma implementação paralela de QA-after-creation permanece no pro
- [ ] `specialist_context` pode ser repassado sem bifurcar o pipeline
