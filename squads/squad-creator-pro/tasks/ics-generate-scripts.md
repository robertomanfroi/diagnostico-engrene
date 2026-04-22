<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: ics-generate-scripts
  task_name: ICS Phases 3-7 — Generate Scripts
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
  - Generate runtime-paths.cjs
  - Generate discover-context.cjs
  - Generate set-active-context.cjs
  - Generate load-context.cjs
  - Generate show-context.cjs
  acceptance_criteria:
  - ics-domain-mapping completo
  - 'Referencia canonica acessivel: `squads/copy/scripts/`'
  - '`squads/c-level/scripts/resolve-squad-workspace-readiness.cjs` acessivel'
  - Apenas scripts missing foram gerados (existing preservados)
  - Todos os scripts seguem o Script Structure Contract
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


# Task: ICS Phases 3-7 — Generate Scripts

**Task ID:** ics-generate-scripts
**Parent:** install-context-stack (stub)
**Purpose:** Gerar os 5 scripts .cjs do context stack adaptados ao dominio do squad
**Orchestrator:** @squad-chief
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent`
**Model:** `Opus` (REQUIRED — scripts precisam adaptacao por dominio, nao sao copy-paste)
**Haiku Eligible:** NO
**Estimated Time:** 30-45min

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CS-002 | Script existente sobrescrito sem backup | Verificar se arquivo ja existe antes de Write() | VETO - BLOCK. Preservar scripts existentes. |
| VETO-CS-003 | Script gerado depende de estado da LLM | Revisar codigo gerado | VETO - BLOCK. 100% deterministico. |
| VETO-CS-004 | Session context salvo fora de .aiox/squad-runtime/ | Verificar path de output | VETO - BLOCK. Runtime data vai em .aiox/. |
| VETO-CS-005 | Script duplica funcionalidade de script existente no squad | Verificar inventario | VETO - BLOCK. Importar, nao duplicar. |

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | ICS Phases 3-7 — Generate Scripts |
| **status** | `pending` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | domain_mapping, config_extract, scripts_inventory (from previous tasks) |
| **output** | 5 scripts .cjs em `squads/{squad}/scripts/` |
| **acceptance_criteria** | 6 criterios testaveis |

---

## Inputs

| Parameter | Type | Required | Source | Validation |
|-----------|------|----------|--------|------------|
| `domain_mapping` | object | Yes | ics-domain-mapping | Contem primary_entity e session_schema |
| `config_extract` | object | Yes | ics-audit | Contem workspace_integration fields |
| `scripts_inventory` | object | Yes | ics-audit | Lista existing/missing/partial |
| `--force` | flag | No | user | Permite sobrescrever (cria backup timestamped) |

---

## Preconditions

- [ ] ics-domain-mapping completo
- [ ] Referencia canonica acessivel: `squads/copy/scripts/`
- [ ] `squads/c-level/scripts/resolve-squad-workspace-readiness.cjs` acessivel

---

## Canonical References

Usar como modelo de referencia (READ-ONLY, nao copiar verbatim):

| Script | Referencia | Adaptar |
|--------|-----------|---------|
| `runtime-paths.cjs` | `squads/copy/scripts/runtime-paths.cjs` | Namespace, paths |
| `discover-context.cjs` | `squads/copy/scripts/discover-context.cjs` | Entidades descobertas |
| `set-active-context.cjs` | `squads/copy/scripts/set-active-context.cjs` | Flags CLI, session schema |
| `load-context.cjs` | `squads/copy/scripts/load-context.cjs` | Dados carregados, readiness checks |
| `show-context.cjs` | `squads/copy/scripts/show-context.cjs` | Formatacao do output |

---

## Generation Rules

1. **Self-contained** — importa apenas runtime-paths.cjs e libs padrao (fs, path, yaml)
2. **Readiness via resolver central** — `squads/c-level/scripts/resolve-squad-workspace-readiness.cjs`
3. **Session context em YAML** — `.aiox/squad-runtime/{namespace}/{entry_agent}/session-context.yaml` (VETO-CS-004)
4. **Zero dependencia de LLM** — 100% deterministico (VETO-CS-003)
5. **Erro = exit code != 0** — mensagem clara no stderr
6. **Importar, nao duplicar** — scripts existentes no squad devem ser importados (VETO-CS-005)

---

## Script Structure Contract

Cada script gerado DEVE seguir:

```javascript
#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const yaml = require('js-yaml');

// Import centralized paths
const runtimePaths = require('./runtime-paths.cjs');

function main() {
  try {
    // ... script logic
  } catch (error) {
    console.error(`ERROR: ${error.message}`);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
} else {
  module.exports = { /* exported functions */ };
}
```

---

## Steps

### Step 3: Generate runtime-paths.cjs

- Namespace derivado do squad name
- Paths para workspace, outputs, runtime session
- Centraliza todos os paths usados pelos demais scripts

### Step 4: Generate discover-context.cjs

- Lista businesses/products disponiveis no workspace
- Adapta entidades descobertas ao dominio (primary_entity)
- Output: JSON com entidades encontradas

### Step 5: Generate set-active-context.cjs

- Aceita flags CLI baseadas no session_schema
- Salva session-context.yaml em `.aiox/squad-runtime/{namespace}/{entry_agent}/`
- Valida que business_slug existe antes de salvar

### Step 6: Generate load-context.cjs

- Le session-context.yaml ativa
- Enriquece com dados do workspace (le read_paths)
- Chama resolve-squad-workspace-readiness.cjs para readiness
- Output: JSON com business_slug, dados enriquecidos e readiness.status

### Step 7: Generate show-context.cjs

- Le contexto carregado via load-context
- Formata como markdown legivel
- Mostra business ativo, readiness status e gaps

---

## Error Handling

| Error | Detection | Recovery |
|-------|-----------|----------|
| Script fails (exit != 0) | Smoke test | Revisar codigo, comparar com referencia copy |
| Partial script conflict | Inventario lista 'partial' | Criar wrapper que importa existente |
| Readiness resolver missing | require() MODULE_NOT_FOUND | Verificar squads/c-level/scripts/ |

---

## Output Contract

```yaml
scripts_generated:  # Array of 5 entries (runtime-paths, discover-context, set-active-context, load-context, show-context)
  - id: "{script-id}"
    path: "squads/{squad}/scripts/{script-id}.cjs"
    status: "generated|existing|skipped"
```

---

## Acceptance Criteria

- [ ] Apenas scripts missing foram gerados (existing preservados)
- [ ] Todos os scripts seguem o Script Structure Contract
- [ ] Session context path usa `.aiox/squad-runtime/` (VETO-CS-004)
- [ ] Nenhum script depende de estado da LLM (VETO-CS-003)
- [ ] Scripts partial tratados com wrapper/import, nao duplicacao (VETO-CS-005)
- [ ] Se --force usado, backup timestamped criado antes de sobrescrever

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `ics-integration` |
| **Trigger** | Scripts gerados (ou existentes preservados) |
| **Passes** | scripts_generated, domain_mapping, config_extract |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-26_
_Author: squad-chief_
