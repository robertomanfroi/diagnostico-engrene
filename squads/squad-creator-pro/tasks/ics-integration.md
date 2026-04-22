<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: ics-integration
  task_name: ICS Phase 8 — Integration
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
  - '.1: Registrar Scripts no Config'
  - '.2: Adicionar Comandos no Entry Agent'
  acceptance_criteria:
  - ics-generate-scripts completo
  - Todos os 5 scripts existem em `squads/{squad}/scripts/
  - config.yaml tem secao `scripts:` com os 5 scripts registrados
  - Entry agent tem comandos *show-context e *set-context
  - Nenhuma entry existente foi duplicada ou removida
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


# Task: ICS Phase 8 — Integration

**Task ID:** ics-integration
**Parent:** install-context-stack (stub)
**Purpose:** Registrar scripts no config.yaml do squad e adicionar comandos no entry agent
**Orchestrator:** @squad-chief
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent`
**Model:** `Opus` (REQUIRED)
**Estimated Time:** 10-15min

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | ICS Phase 8 — Integration |
| **status** | `pending` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | scripts_generated, config_extract (from previous tasks) |
| **output** | config.yaml atualizado + entry agent atualizado |
| **acceptance_criteria** | 3 criterios testaveis |

---

## Inputs

| Parameter | Type | Required | Source | Validation |
|-----------|------|----------|--------|------------|
| `scripts_generated` | array | Yes | ics-generate-scripts | Lista de scripts gerados/existentes |
| `config_extract` | object | Yes | ics-audit | Contem entry_agent e squad_name |

---

## Preconditions

- [ ] ics-generate-scripts completo
- [ ] Todos os 5 scripts existem em `squads/{squad}/scripts/`

---

## Steps

### Step 8.1: Registrar Scripts no Config

Adicionar secao `scripts:` no config.yaml do squad (se nao existir):

```yaml
scripts:
  - id: runtime-paths
    file: "scripts/runtime-paths.cjs"
    description: "Paths centralizados para runtime e workspace"
  - id: discover-context
    file: "scripts/discover-context.cjs"
    description: "Descobrir businesses/products disponiveis"
  - id: set-active-context
    file: "scripts/set-active-context.cjs"
    description: "Setar sessao ativa (business, product, etc.)"
    cli: "node squads/{squad}/scripts/set-active-context.cjs --business=<slug>"
  - id: load-context
    file: "scripts/load-context.cjs"
    description: "Carregar contexto ativo com readiness"
  - id: show-context
    file: "scripts/show-context.cjs"
    description: "Mostrar contexto ativo formatado"
```

**Regra:** Se a secao `scripts:` ja existe, fazer merge preservando entries existentes. Nao duplicar.

### Step 8.2: Adicionar Comandos no Entry Agent

Adicionar no bloco `commands:` do entry agent:

```yaml
- "*show-context - Display active session context (business, readiness, gaps)"
- "*set-context <business> [--product=<slug>] - Set active business/product context"
```

**Regra:** Se os comandos ja existem no agent, nao duplicar.

---

## Error Handling

```yaml
error_handling:
  config_merge_conflict:
    trigger: "Secao scripts ja existe com entries conflitantes"
    detection: "YAML parse encontra IDs duplicados"
    recovery: "Merge manual, preservar existentes, adicionar novos"
    prevention: "Sempre ler config atual antes de editar"

  agent_file_not_found:
    trigger: "Entry agent .md nao encontrado"
    detection: "fs.existsSync() retorna false"
    recovery: "Verificar entry_agent no config_extract"
    prevention: "Validar precondicao"
```

---

## Output Contract

```yaml
integration:
  config_updated: true|false
  config_path: "squads/{squad}/config.yaml"
  scripts_registered: 5
  agent_updated: true|false
  agent_path: "squads/{squad}/agents/{entry_agent}.md"
  commands_added: ["*show-context", "*set-context"]
```

---

## Acceptance Criteria

- [ ] config.yaml tem secao `scripts:` com os 5 scripts registrados
- [ ] Entry agent tem comandos *show-context e *set-context
- [ ] Nenhuma entry existente foi duplicada ou removida

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `ics-validation` |
| **Trigger** | Integration completa |
| **Passes** | integration output |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-26_
_Author: squad-chief_
