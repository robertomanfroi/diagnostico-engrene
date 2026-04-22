<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-documentation
  task_name: Create Documentation (Extension Wrapper)
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Normalize Target
  - Build Delegation Payload
  - Delegate to Base
  - Reconcile Outputs
  acceptance_criteria:
  - squads/squad-creator/tasks/create-documentation.md` existe
  - O chamador entende que este wrapper não possui pipeline documental próprio
  - Se o alvo for um squad, `squad_name` ou `pack_name` está resolvido
  - pack_name` e `squad_name` são reconciliados corretamente
  - A geração documental real é delegada ao base
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


# Task: Create Documentation (Extension Wrapper)

**Task ID:** create-documentation
**Version:** 3.0.0
**Purpose:** Preservar compatibilidade do `squad-creator-pro` enquanto delega a criação documental ao owner canônico no `squad-creator`
**Orchestrator:** @pedro-valerio
**Mode:** Delegation-first
**Quality Standard:** Herdado da task base

---

## Purpose

Este wrapper existe para manter compatibilidade com workflows do `squad-creator-pro` que ainda chamam `create-documentation` após criar agents, workflows ou squads.

**Regra não negociável:** documentação estrutural compartilhada deve viver no base quando o comportamento é o mesmo. O pro só acrescenta contexto; não mantém um segundo processo completo de documentação.

Owner canônico:

- `squads/squad-creator/tasks/create-documentation.md`

O papel desta task é apenas:

1. normalizar inputs legados do pro;
2. reconciliar `pack_name` com `squad_name` quando aplicável;
3. transferir contexto adicional do pro para a geração documental;
4. delegar a execução para a task base;
5. devolver o resultado no formato esperado pelos chamadores do pro.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `artifact_name` | string | Yes | Nome do artefato criado |
| `artifact_type` | enum | No | `agent`, `workflow` ou `squad` |
| `squad_name` | string | No | Nome canônico do squad alvo |
| `pack_name` | string | No | Alias legado usado no pro; deve virar `squad_name` |
| `source_artifacts` | list | No | Artefatos de research ou discovery relevantes |
| `integration_notes` | object | No | Restrições ou observações contextuais do pro |

---

## Preconditions

- [ ] `squads/squad-creator/tasks/create-documentation.md` existe
- [ ] O chamador entende que este wrapper não possui pipeline documental próprio
- [ ] Se o alvo for um squad, `squad_name` ou `pack_name` está resolvido

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

### Step 2: Build Delegation Payload

```yaml
build_base_payload:
  required_fields:
    - artifact_name
  optional_fields:
    - artifact_type
    - squad_name
    - source_artifacts
    - integration_notes
  rule: >
    O pro pode enriquecer o contexto documental, mas não redefine templates,
    padrões de seções ou fluxo de geração documental do base.
```

### Step 3: Delegate to Base

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/create-documentation.md"
  payload:
    - artifact_name
    - artifact_type
    - squad_name
    - source_artifacts
    - integration_notes
  prohibition:
    - "Do NOT maintain a parallel create-documentation methodology in squad-creator-pro"
```

### Step 4: Reconcile Outputs

```yaml
reconcile_outputs:
  return_shape:
    delegated_task: "squads/squad-creator/tasks/create-documentation.md"
    normalized_squad_name: "{squad_name}"
    execution_mode: "base-delegated"
```

---

## Output

```yaml
output:
  name: delegated_documentation_creation
  format: yaml
  structure:
    delegated_task: "squads/squad-creator/tasks/create-documentation.md"
    normalized_squad_name: "{squad_name}"
    status: "delegated"
```

---

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] A geração documental real é delegada ao base
- [ ] Nenhuma metodologia paralela de documentação permanece no pro
- [ ] Workflows do pro que dependem de `create-documentation` continuam compatíveis

---

## Veto Conditions

- `squad_name` e `pack_name` apontarem para squads diferentes
- A task base `create-documentation.md` não existir
- O pro tentar redefinir templates e seções que já pertencem ao base

---

## Related Documents

- `squads/squad-creator/tasks/create-documentation.md` -- owner canônico

---

_Task Version: 3.0.0_
_Role: compatibility wrapper for upgrade-pack delegation_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed create-documentation output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
