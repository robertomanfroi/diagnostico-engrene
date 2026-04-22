<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-greeting-script
  task_name: Create Greeting Script (Extension Wrapper)
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
  - O workflow do pro usa um `task_ref` local e consistente
  - A lógica real de greeting continua centralizada no base
  - Nenhum pipeline paralelo de greeting permanece aqui
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


# Task: Create Greeting Script (Extension Wrapper)

**Task ID:** create-greeting-script
**Version:** 3.0.0
**Purpose:** Preservar compatibilidade do `squad-creator-pro` enquanto delega a criação real do greeting determinístico ao owner canônico no `squad-creator`
**Orchestrator:** @squad-chief
**Mode:** Delegation-first
**Quality Standard:** Herdado da task base

---

## Purpose

Este wrapper existe para que workflows do `squad-creator-pro` usem um `task_ref` local e estável, sem depender de path foreign.

O owner canônico permanece em:

- `squads/squad-creator/tasks/create-greeting-script.md`

O papel desta task é apenas:

1. normalizar o alvo do squad;
2. preservar o contexto de `install-workspace-context`;
3. delegar a geração real do greeting para o base;
4. devolver os outputs esperados pelo workflow do pro.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | No | Nome canônico do squad alvo |
| `pack_name` | string | No | Alias legado; deve virar `squad_name` |
| `context_sources` | list | No | Scripts/context sources instalados previamente |
| `entry_agent` | string | No | Agent a ser atualizado com STEP 3.5 |

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
  task: "squads/squad-creator/tasks/create-greeting-script.md"
  payload:
    - squad_name
    - context_sources
    - entry_agent
  prohibition:
    - "Do NOT maintain a second greeting-generation methodology in squad-creator-pro"
```

### Step 3: Reconcile Outputs

```yaml
reconcile_outputs:
  outputs:
    - "squads/{squad_name}/scripts/generate-{squad_name}-greeting.cjs"
    - "entry agent atualizado com STEP 3.5"
  return_shape:
    delegated_task: "squads/squad-creator/tasks/create-greeting-script.md"
    execution_mode: "base-delegated"
```

---

## Acceptance Criteria

- [ ] O workflow do pro usa um `task_ref` local e consistente
- [ ] A lógica real de greeting continua centralizada no base
- [ ] Nenhum pipeline paralelo de greeting permanece aqui

---

## Related Documents

- `squads/squad-creator/tasks/create-greeting-script.md` -- owner canônico
- `workflows/wf-install-workspace-context.yaml` -- consumidor local no pro

---

_Task Version: 3.0.0_
_Role: compatibility wrapper for upgrade-pack delegation_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed create-greeting-script output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** Execution halts on quality gate failure
