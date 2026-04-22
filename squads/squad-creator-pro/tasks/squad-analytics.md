<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-analytics
  task_name: Squad Analytics (Extension Wrapper)
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
  - squads/squad-creator/tasks/squad-analytics.md` existe
  - squads/squad-creator/scripts/squad-analytics.py` existe
  - O chamador entende que este wrapper não implementa analytics paralelos
  - pack_name` e `squad_name` são reconciliados corretamente
  - As métricas e a análise real são delegadas ao base
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


# Task: Squad Analytics (Extension Wrapper)

**Task ID:** squad-analytics
**Version:** 3.0.0
**Purpose:** Preservar compatibilidade do `squad-creator-pro` enquanto delega analytics e interpretação de qualidade ao owner canônico no `squad-creator`
**Orchestrator:** @squad-chief
**Mode:** Delegation-first
**Quality Standard:** Herdado da task e do worker script base

---

## Purpose

Este wrapper existe para manter compatibilidade com `*squad-analytics` e com chamadores do pro que ainda esperam uma task local com este nome.

**Regra não negociável:** a coleta determinística de métricas e a interpretação básica de analytics pertencem ao base quando o comportamento é compartilhado.

Owners canônicos:

- `squads/squad-creator/tasks/squad-analytics.md`
- `squads/squad-creator/scripts/squad-analytics.py`

O papel deste wrapper é:

1. normalizar inputs legados do pro;
2. preservar filtros e contexto adicional do upgrade-pack;
3. delegar a execução para a task base;
4. devolver o relatório no formato esperado pelos chamadores do pro.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | No | Squad alvo |
| `pack_name` | string | No | Alias legado usado no pro; deve virar `squad_name` |
| `detailed` | boolean | No | Exibe contagens detalhadas |
| `quality_audit` | boolean | No | Inclui checagem de mínimos |
| `format` | enum | No | `table` ou `json` |
| `analyze` | boolean | No | Pede interpretação adicional |
| `recommendations` | boolean | No | Pede recomendações priorizadas |

---

## Preconditions

- [ ] `squads/squad-creator/tasks/squad-analytics.md` existe
- [ ] `squads/squad-creator/scripts/squad-analytics.py` existe
- [ ] O chamador entende que este wrapper não implementa analytics paralelos

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
  task: "squads/squad-creator/tasks/squad-analytics.md"
  worker_script: "squads/squad-creator/scripts/squad-analytics.py"
  payload:
    - squad_name
    - detailed
    - quality_audit
    - format
    - analyze
    - recommendations
  prohibition:
    - "Do NOT maintain a second analytics methodology in squad-creator-pro"
    - "Do NOT fork quality thresholds or counting logic locally"
```

### Step 3: Reconcile Outputs

```yaml
reconcile_outputs:
  return_shape:
    delegated_task: "squads/squad-creator/tasks/squad-analytics.md"
    delegated_script: "squads/squad-creator/scripts/squad-analytics.py"
    normalized_squad_name: "{squad_name}"
    execution_mode: "base-delegated"
```

---

## Output

```yaml
output:
  name: delegated_squad_analytics
  format: yaml
  structure:
    delegated_task: "squads/squad-creator/tasks/squad-analytics.md"
    delegated_script: "squads/squad-creator/scripts/squad-analytics.py"
    normalized_squad_name: "{squad_name}"
    status: "delegated"
```

---

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] As métricas e a análise real são delegadas ao base
- [ ] Nenhum cálculo paralelo de analytics permanece no pro
- [ ] Chamadas existentes do pro continuam compatíveis

---

## Veto Conditions

- `squad_name` e `pack_name` apontarem para squads diferentes
- A task ou o script base não existirem
- O pro tentar redefinir thresholds ou métricas que já pertencem ao base

---

## Related Documents

- `squads/squad-creator/tasks/squad-analytics.md` -- owner canônico
- `squads/squad-creator/scripts/squad-analytics.py` -- execução determinística

---

_Task Version: 3.0.0_
_Role: compatibility wrapper for upgrade-pack delegation_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed squad-analytics output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
