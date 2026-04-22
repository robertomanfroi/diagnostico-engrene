<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad-inventory
  task_name: Upgrade Squad - Inventory
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
  - Carregar o baseline herdado
  - Enriquecer para o overlay pro
  acceptance_criteria:
  - O task canônico do base é carregado antes do enriquecimento
  - O inventário estrutural não é redefinido localmente
  - O output já separa baseline estrutural de sinais avançados do pack
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


# Task: Upgrade Squad - Inventory

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-inventory` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: upgrade-squad-inventory
name: "Upgrade Squad Inventory"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Wrapper fino sobre o inventário estrutural canônico do base, com leitura adicional dos sinais avançados que o pack pro precisa."
```

## Purpose

Executar primeiro o inventário estrutural definido em `squads/squad-creator/tasks/upgrade-squad-inventory.md`. Depois disso, enriquecer o output com sinais avançados do target: `workspace_integration`, `artifact_contracts`, `supported_modes`, `journey_log`, `model-routing`, `test-cases`, `minds/` e ativos de runtime.

## Workflow / Steps

### Step 1: Carregar o baseline herdado

- Ler `squads/squad-creator/tasks/upgrade-squad-inventory.md` por completo.
- Executar o inventário estrutural sem alterar os critérios do base.

### Step 2: Enriquecer para o overlay pro

- Detectar se o target já possui `workspace_integration`, `artifact_contracts` e `supported_modes`.
- Detectar presença de `minds/`, `config/model-routing.yaml`, `test-cases/` e ativos runtime em `.aiox/`.
- Marcar quais desses sinais são nativos, ausentes ou parciais.

## Output

```yaml
output:
  schema:
    structural_inventory: {}
    advanced_signals:
      workspace_contract: "missing | partial | present"
      artifact_contracts: "missing | partial | present"
      supported_modes: "missing | partial | present"
      journey_log: "missing | partial | present"
      model_routing: "missing | present"
      minds: "missing | present"
      runtime_assets: []
```

## Acceptance Criteria

- [ ] O task canônico do base é carregado antes do enriquecimento
- [ ] O inventário estrutural não é redefinido localmente
- [ ] O output já separa baseline estrutural de sinais avançados do pack

## Related Documents

- `squads/squad-creator/tasks/upgrade-squad-inventory.md`
- `upgrade-squad-gap.md`
