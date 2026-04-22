<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: ics-audit
  task_name: ICS Phase 1 — Audit
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
  - '.1: Ler Config do Squad'
  - '.2: Inventariar Scripts Existentes'
  acceptance_criteria:
  - 'Squad existe: `squads/{squad_name}/` presente'
  - config.yaml` existe e e parseavel
  - 'Referencia canonica acessivel: `squads/copy/scripts/`'
  - Eligibility gate avaliou workspace_integration.level
  - Config extract contem todos os campos requeridos
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


# Task: ICS Phase 1 — Audit

**Task ID:** ics-audit
**Parent:** install-context-stack (stub)
**Purpose:** Ler config.yaml do squad alvo, verificar eligibility gate e inventariar scripts existentes vs faltantes
**Orchestrator:** @squad-chief
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent`
**Model:** `Opus` (REQUIRED)
**Estimated Time:** 10-15min

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CS-001 | Squad sem workspace_integration ou level < controlled_runtime_consumer | Ler config.yaml | VETO - BLOCK. Squad nao precisa de context stack. |
| VETO-CS-002 | Script existente sobrescrito sem backup | Verificar se arquivo ja existe antes de Write() | VETO - BLOCK. Preservar scripts existentes. |

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | ICS Phase 1 — Audit |
| **status** | `pending` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `squad_name` (required), `--force` flag (optional) |
| **output** | Audit report com eligibility, config extract e scripts inventory |
| **acceptance_criteria** | 4 criterios testaveis |

---

## Inputs

| Parameter | Type | Required | Source | Validation |
|-----------|------|----------|--------|------------|
| `squad_name` | string | Yes | parent task | Squad existe em `squads/{squad_name}/` |
| `--force` | flag | No | user | Se true, permite sobrescrever scripts existentes |

---

## Preconditions

- [ ] Squad existe: `squads/{squad_name}/` presente
- [ ] `config.yaml` existe e e parseavel
- [ ] Referencia canonica acessivel: `squads/copy/scripts/`

---

## Eligibility Gate

| workspace_integration.level | Elegivel? | Motivo |
|----------------------------|-----------|--------|
| `none` | NO | Squad nao interage com workspace |
| `read_only` | NO | Leitura pontual, sem sessao ativa |
| `controlled_runtime_consumer` | YES | Consome workspace com sessao ativa |
| `workspace_first` | YES | Workspace e fonte primaria |

Se o squad alvo tem level `none` ou `read_only`, esta task da VETO (VETO-CS-001) e sugere alternativa (greeting simples sem context stack).

---

## Steps

### Step 1.1: Ler Config do Squad

```yaml
action: read
files:
  - "squads/{squad_name}/config.yaml"
  - "squads/{squad_name}/agents/{entry_agent}.md"
extract:
  - name
  - entry_agent
  - workspace_integration.level
  - workspace_integration.read_paths
  - workspace_integration.write_paths
  - workspace_integration.readiness_context_type
  - workspace_integration.canonical_outputs_root
```

### Step 1.2: Inventariar Scripts Existentes

```yaml
check_scripts:
  runtime_paths: "squads/{squad_name}/scripts/runtime-paths.cjs"
  discover_context: "squads/{squad_name}/scripts/discover-context.cjs"
  set_active_context: "squads/{squad_name}/scripts/set-active-context.cjs"
  load_context: "squads/{squad_name}/scripts/load-context.cjs"
  show_context: "squads/{squad_name}/scripts/show-context.cjs"

output:
  existing: []    # scripts que ja existem (PRESERVAR, nao sobrescrever)
  missing: []     # scripts que precisam ser gerados
  partial: []     # scripts com nome diferente (ex: load-workspace-context.cjs)
```

**Regra:** Se um script ja existe e funciona, NAO sobrescrever (VETO-CS-002). Se existe mas com nome diferente (ex: `load-workspace-context.cjs`), avaliar se pode ser adaptado ou se precisa de novo script que importa o existente (VETO-CS-005).

---

## Output Contract

```yaml
ics_audit:
  squad_name: "{squad_name}"
  eligible: true|false
  workspace_level: "{level do config.yaml}"
  config_extract:
    name: ""
    entry_agent: ""
    read_paths: []
    write_paths: []
    readiness_context_type: ""
    canonical_outputs_root: ""
  scripts_inventory:
    existing: []
    missing: []
    partial: []
  veto: null|"VETO-CS-001: level insufficient"
```

---

## Error Handling

```yaml
error_handling:
  config_not_found:
    trigger: "config.yaml nao existe"
    detection: "fs.existsSync() retorna false"
    recovery: "BLOCK — squad precisa de config.yaml"

  config_not_parseable:
    trigger: "YAML invalido"
    detection: "yaml.load() throws"
    recovery: "BLOCK — corrigir config.yaml antes de continuar"
```

---

## Acceptance Criteria

- [ ] Eligibility gate avaliou workspace_integration.level
- [ ] Config extract contem todos os campos requeridos
- [ ] Scripts inventory classifica cada script como existing/missing/partial
- [ ] VETO-CS-001 bloqueia squads com level < controlled_runtime_consumer

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `ics-domain-mapping` |
| **Trigger** | Audit completo com eligible=true |
| **Passes** | config_extract, scripts_inventory |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-26_
_Author: squad-chief_
