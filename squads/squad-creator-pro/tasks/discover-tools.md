<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: discover-tools
  task_name: Discover Tools for Squad (Extension Wrapper)
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
  - Normalize Discovery Context
  - Delegate to Pro Workflow
  - Reconcile Outputs
  acceptance_criteria:
  - workflows/wf-discover-tools.yaml` existe no `squad-creator-pro
  - data/tool-registry.yaml` existe
  - O chamador entende que este wrapper não possui pipeline próprio
  - O contexto de domínio e casos de uso já está minimamente definido
  - Chamadas legadas a `discover-tools` continuam funcionando
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
  Domain: Tactical
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Discover Tools for Squad (Extension Wrapper)

**Task ID:** discover-tools
**Version:** 3.1.0
**Purpose:** Preservar compatibilidade do `squad-creator-pro` enquanto delega a descoberta profunda de ferramentas ao workflow canônico do próprio upgrade-pack
**Orchestrator:** @squad-chief
**Mode:** Delegation-first
**Quality Standard:** Herdado de `workflows/wf-discover-tools.yaml`

---

## Purpose

Este arquivo existe para manter compatibilidade com chamadas legadas que ainda invocam `discover-tools` como task direta.

No `squad-creator-pro`, o owner canônico da descoberta profunda de ferramentas é:

- `workflows/wf-discover-tools.yaml`

O papel desta task é apenas:

1. normalizar inputs legados;
2. preservar contexto adicional passado por workflows do pro;
3. delegar a execução para o workflow canônico do pro;
4. devolver outputs no formato esperado pelos chamadores antigos.

**Regra não negociável:** o `squad-creator-pro` não deve manter um segundo monólito de discovery quando já existe um workflow especializado e mais forte.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `domain` | string | Yes | Domínio ou squad alvo |
| `use_cases` | list | Yes | Casos de uso principais |
| `existing_tools` | list | No | Ferramentas já conhecidas |
| `capability_gaps` | list | No | Gaps conhecidos |
| `budget_tier` | enum | No | `free_only`, `low_cost`, `enterprise` |
| `priority_capabilities` | list | No | Capacidades a priorizar |
| `search_depth` | enum | No | `quick`, `standard`, `exhaustive` |
| `scope_hint` | string | No | Clarificação para domínios ambíguos |

---

## Preconditions

- [ ] `workflows/wf-discover-tools.yaml` existe no `squad-creator-pro`
- [ ] `data/tool-registry.yaml` existe
- [ ] O chamador entende que este wrapper não possui pipeline próprio
- [ ] O contexto de domínio e casos de uso já está minimamente definido

---

## Workflow

### Step 1: Normalize Discovery Context

```yaml
normalize_context:
  rules:
    - domain is mandatory
    - if use_cases missing:
        action: block_and_elicit
    - if search_depth missing:
        default: standard
    - if budget_tier missing:
        default: low_cost
```

### Step 2: Delegate to Pro Workflow

```yaml
delegate_to_workflow:
  workflow: "workflows/wf-discover-tools.yaml"
  payload:
    - domain
    - use_cases
    - existing_tools
    - capability_gaps
    - budget_tier
    - priority_capabilities
    - search_depth
    - scope_hint
  prohibition:
    - "Do NOT maintain a second standalone discovery methodology here"
    - "Do NOT fork scoring, classification or recommendation logic outside the workflow"
```

### Step 3: Reconcile Outputs

```yaml
reconcile_outputs:
  expected_outputs:
    - ".aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md"
    - ".aiox/squad-runtime/discovery/{domain}/capability-tools.yaml"
    - ".aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md"
  return_shape:
    delegated_workflow: "workflows/wf-discover-tools.yaml"
    execution_mode: "pro-workflow-delegated"
    domain: "{domain}"
```

---

## Output

```yaml
output:
  name: delegated_tool_discovery
  format: yaml
  structure:
    delegated_workflow: "workflows/wf-discover-tools.yaml"
    domain: "{domain}"
    status: "delegated"
```

---

## Acceptance Criteria

- [ ] Chamadas legadas a `discover-tools` continuam funcionando
- [ ] A execução real ocorre no workflow canônico do pro
- [ ] Nenhum pipeline paralelo de discovery permanece nesta task
- [ ] Os outputs continuam compatíveis com chamadores antigos

---

## Veto Conditions

- `workflows/wf-discover-tools.yaml` não existir
- `domain` não for fornecido
- `use_cases` não forem fornecidos
- Algum chamador depender de fases que só existiam no monólito antigo

---

## Related Documents

- `workflows/wf-discover-tools.yaml` -- owner canônico no pro
- `data/tool-registry.yaml` -- catálogo e memória de ferramentas
- `squads/squad-creator/tasks/discover-tools.md` -- wrapper base com detecção de pro mode

---

_Task Version: 3.1.0_
_Role: compatibility wrapper for upgrade-pack delegation_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed discover-tools output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
