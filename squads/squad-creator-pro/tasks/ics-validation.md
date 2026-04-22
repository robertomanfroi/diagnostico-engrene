<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: ics-validation
  task_name: ICS Phase 9 — Validation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - '.1: Smoke Tests'
  - '.2: Validacao Estrutural'
  acceptance_criteria:
  - ics-integration completa
  - Todos os 5 scripts existem em `squads/{squad}/scripts/
  - config.yaml e entry agent atualizados
  - Todos retornam exit code 0 com input valido
  - set-active-context` cria `session-context.yaml` em `.aiox/squad-runtime/
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: ICS Phase 9 — Validation

**Task ID:** ics-validation
**Parent:** install-context-stack (stub)
**Purpose:** Smoke test cada script, validar criacao de session-context.yaml e verificar integracao completa
**Orchestrator:** @squad-chief
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent`
**Model:** `Opus` (REQUIRED)
**Estimated Time:** 10-15min

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | ICS Phase 9 — Validation |
| **status** | `pending` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `squad_name`, integration output (from ics-integration) |
| **output** | Validation report com smoke test results |
| **acceptance_criteria** | 5 criterios testaveis |

---

## Inputs

| Parameter | Type | Required | Source | Validation |
|-----------|------|----------|--------|------------|
| `squad_name` | string | Yes | parent task | Squad com scripts instalados |
| `integration` | object | Yes | ics-integration | Confirma config e agent atualizados |

---

## Preconditions

- [ ] ics-integration completa
- [ ] Todos os 5 scripts existem em `squads/{squad}/scripts/`
- [ ] config.yaml e entry agent atualizados

---

## Steps

### Step 9.1: Smoke Tests

```bash
# 1. runtime-paths carrega sem erro
node squads/{squad}/scripts/runtime-paths.cjs 2>&1; echo "EXIT: $?"

# 2. discover-context lista businesses
node squads/{squad}/scripts/discover-context.cjs 2>&1; echo "EXIT: $?"

# 3. set-active-context com business valido
node squads/{squad}/scripts/set-active-context.cjs --business=aiox 2>&1; echo "EXIT: $?"

# 4. load-context carrega sessao
node squads/{squad}/scripts/load-context.cjs 2>&1; echo "EXIT: $?"

# 5. show-context produz markdown
node squads/{squad}/scripts/show-context.cjs 2>&1; echo "EXIT: $?"
```

### Step 9.2: Validacao Estrutural

- [ ] Todos os 5 scripts existem em `squads/{squad}/scripts/`
- [ ] Todos retornam exit code 0 com input valido
- [ ] `set-active-context` cria `session-context.yaml` em `.aiox/squad-runtime/`
- [ ] `load-context` retorna JSON/YAML com `business_slug` e `readiness.status`
- [ ] `show-context` produz markdown legivel com business ativo

---

## Error Handling

```yaml
error_handling:
  smoke_test_fails:
    trigger: "Script retorna exit code != 0"
    detection: "Exit code check"
    recovery: "Revisar codigo gerado, comparar com referencia. Fallback para Hybrid."
    prevention: "Seguir script structure contract na geracao"

  session_context_not_created:
    trigger: "set-active-context nao cria session-context.yaml"
    detection: "fs.existsSync() retorna false apos execucao"
    recovery: "Verificar paths em runtime-paths.cjs e permissoes de diretorio"
    prevention: "Usar mkdir recursive antes de writeFileSync"
```

---

## Output Contract

```yaml
validation:
  smoke_tests:
    runtime_paths: "PASS|FAIL"
    discover_context: "PASS|FAIL"
    set_active_context: "PASS|FAIL"
    load_context: "PASS|FAIL"
    show_context: "PASS|FAIL"
  structural:
    all_scripts_exist: true|false
    session_context_created: true|false
    load_returns_readiness: true|false
    show_produces_markdown: true|false
  final_result: "PASS|FAIL"
```

---

## Acceptance Criteria

- [ ] Todos os 5 smoke tests passam (exit code 0)
- [ ] set-active-context cria session-context.yaml em `.aiox/squad-runtime/`
- [ ] load-context retorna JSON com business_slug e readiness.status
- [ ] show-context produz markdown legivel
- [ ] final_result e PASS

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `create-greeting-script` (parent task handoff) |
| **Trigger** | Validation PASS |
| **Executor** | @squad-chief |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-26_
_Author: squad-chief_
