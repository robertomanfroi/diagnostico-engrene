<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: sync-ide-skills
  task_name: Sync IDE Skills (Extension Wrapper)
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
  - Normalize Target
  - Delegate to Base
  - Reconcile Outputs
  acceptance_criteria:
  - squads/squad-creator/tasks/sync-ide-skills.md` existe
  - squads/squad-creator/scripts/sync-ide-skills.py` existe
  - O chamador entende que este wrapper não possui engine própria de sync
  - pack_name` e `squad_name` são reconciliados corretamente
  - A sincronização real é delegada ao base
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


# Task: Sync IDE Skills (Extension Wrapper)

**Task ID:** sync-ide-skills
**Version:** 3.0.0
**Purpose:** Preservar compatibilidade do `squad-creator-pro` enquanto delega a sincronização real de skills para o owner canônico no `squad-creator`
**Orchestrator:** @squad-chief
**Mode:** Delegation-first
**Quality Standard:** Herdado da task e do worker script base

---

## Purpose

Este wrapper existe para manter compatibilidade com comandos e handoffs do `squad-creator-pro` que ainda chamam `sync-ide-skills` diretamente.

**Regra não negociável:** a lógica de sincronização multi-IDE não deve ser mantida em paralelo no pro quando o comportamento é o mesmo do base.

Owners canônicos:

- `squads/squad-creator/tasks/sync-ide-skills.md`
- `squads/squad-creator/scripts/sync-ide-skills.py`

O papel deste wrapper é apenas:

1. normalizar inputs legados do pro;
2. reconciliar `pack_name` com `squad_name` quando necessário;
3. delegar a sincronização para a task e o script canônicos do base;
4. devolver o resultado no formato esperado pelos chamadores do pro.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `type` | enum | Yes | `agent`, `task`, `workflow` ou `squad` |
| `name` | string | Yes | Nome do componente a sincronizar |
| `squad_name` | string | No | Nome canônico do squad alvo |
| `pack_name` | string | No | Alias legado usado no pro; deve virar `squad_name` |
| `ides` | list | No | IDEs alvo |
| `dry_run` | boolean | No | Executa preview sem escrever |
| `force` | boolean | No | Permite sobrescrita |

---

## Preconditions

- [ ] `squads/squad-creator/tasks/sync-ide-skills.md` existe
- [ ] `squads/squad-creator/scripts/sync-ide-skills.py` existe
- [ ] O chamador entende que este wrapper não possui engine própria de sync

---

## Workflow

### Step 1: Normalize Target

```yaml
normalize_target:
  rules:
    - if: "squad_name is empty AND pack_name exists"
      then: "set squad_name = pack_name"
    - if: "both squad_name and pack_name exist AND differ"
      then: "block and reconcile target"
```

### Step 2: Delegate to Base

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/sync-ide-skills.md"
  worker_script: "squads/squad-creator/scripts/sync-ide-skills.py"
  payload:
    - type
    - name
    - squad_name
    - ides
    - dry_run
    - force
  prohibition:
    - "Do NOT maintain a second sync methodology in squad-creator-pro"
    - "Do NOT fork IDE destination rules locally"
```

### Step 3: Reconcile Outputs

```yaml
reconcile_outputs:
  return_shape:
    delegated_task: "squads/squad-creator/tasks/sync-ide-skills.md"
    delegated_script: "squads/squad-creator/scripts/sync-ide-skills.py"
    normalized_squad_name: "{squad_name}"
    execution_mode: "base-delegated"
```

---

## Output

```yaml
output:
  name: delegated_sync
  format: yaml
  structure:
    delegated_task: "squads/squad-creator/tasks/sync-ide-skills.md"
    delegated_script: "squads/squad-creator/scripts/sync-ide-skills.py"
    normalized_squad_name: "{squad_name}"
    status: "delegated"
```

---

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] A sincronização real é delegada ao base
- [ ] Nenhuma engine paralela de sync permanece no pro
- [ ] Chamadas existentes do pro continuam compatíveis

---

## Veto Conditions

- `squad_name` e `pack_name` apontarem para squads diferentes
- A task ou o worker script base não existirem
- O pro tentar redefinir regras de destino ou formato que já pertencem ao base

---

## Related Documents

- `squads/squad-creator/tasks/sync-ide-skills.md` -- owner canônico
- `squads/squad-creator/scripts/sync-ide-skills.py` -- execução determinística

---

_Task Version: 3.0.0_
_Role: compatibility wrapper for upgrade-pack delegation_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed sync-ide-skills output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
