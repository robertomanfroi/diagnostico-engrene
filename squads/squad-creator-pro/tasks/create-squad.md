<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-squad
  task_name: Create Complete Squad (Extension Contract Adapter)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  action_items:
    - Normalize Target Squad
    - Route by Invocation Mode
    - Execute Internal Contract Actions
    - Delegate Downstream Creation
  acceptance_criteria:
    - "workflows/wf-create-squad.yaml existe"
    - "workflows/wf-context-aware-create-squad.yaml existe"
    - "o adapter não mantém pipeline end-to-end paralelo"
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

# Task: Create Complete Squad (Extension Contract Adapter)

**Task ID:** create-squad  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` sem reintroduzir um segundo monólito de criação

## Canonical Owners

- `workflows/wf-create-squad.yaml` como router principal do pack
- `workflows/wf-context-aware-create-squad.yaml` como owner greenfield/resume
- `tasks/create-agent.md`, `tasks/create-task.md`, `tasks/create-workflow.md` e `tasks/optimize-workflow.md` para as etapas downstream

## Supported Actions

- `delegate_full_creation`
- `persist_creation_plan`
- `enforce_native_scope_gate`
- `create_architecture`

## Inputs

- `squad_name` é preferido; `pack_name` é alias legado
- `action` defaulta para `delegate_full_creation`
- `creation_plan_path`, `prd_path` e `context_payload` carregam artefatos já produzidos

## Preconditions

- [ ] `workflows/wf-create-squad.yaml` existe
- [ ] `workflows/wf-context-aware-create-squad.yaml` existe
- [ ] o runtime `.aiox/squad-runtime/create-squad/{squad_name}/` pode ser persistido

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "action vazio"
      then: "set action = delegate_full_creation"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

route_by_action:
  delegate_full_creation:
    owner: "workflows/wf-create-squad.yaml"
  internal_actions:
    owner: "workflows/wf-context-aware-create-squad.yaml"
    allowed:
      - persist_creation_plan
      - enforce_native_scope_gate
      - create_architecture

internal_contracts:
  persist_creation_plan:
    outputs:
      - ".aiox/squad-runtime/create-squad/{squad_name}/creation-plan.yaml"
      - "docs/projects/{squad_name}/prd.md"
  enforce_native_scope_gate:
    outputs:
      - ".aiox/squad-runtime/create-squad/{squad_name}/state.json"
      - "docs/projects/{squad_name}/epics/"
  create_architecture:
    outputs:
      - ".aiox/squad-runtime/create-squad/{squad_name}/workspace-integration-level.yaml"
      - ".aiox/squad-runtime/create-squad/{squad_name}/architecture-decision-record.yaml"

downstream_creation:
  delegates_to:
    - create-agent.md
    - create-task.md
    - create-workflow.md
    - optimize-workflow.md
  prohibition:
    - "Do NOT reintroduce local end-to-end creation phases here"
```

## Output

```yaml
output:
  action: "{action}"
  normalized_squad_name: "{squad_name}"
  emitted_artifacts:
    - ".aiox/squad-runtime/create-squad/{squad_name}/*"
    - "docs/projects/{squad_name}/*"
  status: "delegated-or-contracted"
```

## Acceptance Criteria

- [ ] chamadas diretas a `create-squad` são roteadas para `wf-create-squad.yaml`
- [ ] as ações internas usadas por `wf-context-aware-create-squad` estão explicitamente documentadas
- [ ] nenhum pipeline end-to-end paralelo permanece neste arquivo
- [ ] ownership downstream fica explícito

## Veto Conditions

- `create-squad.md` tenta recriar localmente o fluxo completo
- `squad_name` e `pack_name` apontam para squads diferentes
- algum workflow canônico obrigatório não existe
