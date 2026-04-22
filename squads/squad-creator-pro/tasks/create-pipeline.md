<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-pipeline
  task_name: Create Pipeline Scaffolding (Extension Wrapper)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  action_items:
    - Normalize Target Squad
    - Delegate to Base Task
    - Reconcile Outputs
  acceptance_criteria:
    - "squads/squad-creator/tasks/create-pipeline.md existe"
    - "pack_name e squad_name são reconciliados corretamente"
    - "o wrapper não mantém scaffolding paralelo"
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

# Task: Create Pipeline Scaffolding (Extension Wrapper)

**Task ID:** create-pipeline  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` delegando a criação real de pipeline scaffolding ao owner canônico do base

## Canonical Owner

- `squads/squad-creator/tasks/create-pipeline.md`
- `squads/squad-creator/workflows/wf-create-pipeline.yaml`

## Inputs

- `phase_definitions` é obrigatório
- `squad_name` é preferido; `pack_name` é alias legado
- `requirements` e `item_noun` refinam o scaffold

## Preconditions

- [ ] `squads/squad-creator/tasks/create-pipeline.md` existe
- [ ] os templates do pipeline existem no base
- [ ] o alvo resolve para `squads/{squad_name}/`

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

delegate_to_base:
  task: "squads/squad-creator/tasks/create-pipeline.md"
  payload:
    - squad_name
    - phase_definitions
    - requirements
    - item_noun
  prohibition:
    - "Do NOT keep local references to removed pipeline templates inside squad-creator-pro"
    - "Do NOT fork pipeline scaffolding logic locally"

reconcile_outputs:
  delegated_task: "squads/squad-creator/tasks/create-pipeline.md"
  primary_outputs:
    - "squads/{squad_name}/scripts/{squad_name}.sh"
    - "squads/{squad_name}/templates/pipeline/prompt.md"
    - "squads/{squad_name}/lib/"
  execution_mode: "base-delegated"
```

## Output

```yaml
output:
  delegated_task: "squads/squad-creator/tasks/create-pipeline.md"
  normalized_squad_name: "{squad_name}"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] a criação real do scaffolding é delegada ao base
- [ ] nenhuma dependência quebrada de template/data permanece no pro
- [ ] chamadas existentes do pro continuam compatíveis
