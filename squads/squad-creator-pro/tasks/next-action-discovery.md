<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: next-action-discovery
  task_name: Next Action -- Discovery
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Locate Greeting Script
  - Locate Context Sources
  - Extract Existing Commands
  - Identify User Friction Points
  acceptance_criteria:
  - Greeting script located and path recorded
  - Context sources mapped (loader, resolver, writer, runtime files)
  - Canonical commands extracted from config/agents/tasks
  - User friction points identified from greeting analysis
  - Discovery map YAML output generated
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Next Action -- Discovery

**Task ID:** next-action-discovery
**Parent Task:** `next-action.md`
**Purpose:** Map greeting scripts, context loaders, runtime files, and existing gaps for a target squad
**Orchestrator:** @squad-chief
**Execution Type:** `Agent`
**Model:** `Opus`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Next Action -- Discovery |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `squad_name` |
| **output** | Discovery map YAML |
| **action_items** | 4 steps |
| **acceptance_criteria** | All structural sources mapped with zero inference |

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-NA-001 | Squad sem greeting custom | Verificar se existe `generate-*-greeting.*` ou equivalente | VETO - BLOCK. Sem greeting custom, aplicar outro padrao primeiro. |
| VETO-NA-002 | Heuristica sem fonte estrutural de contexto | Verificar se squad possui `load-context`, `runtime-paths`, `session-context` ou equivalentes | VETO - BLOCK. Nao inferir `Next Action` por intuicao solta. |

---

## Quando Esta Task Se Aplica

Use esta task quando o squad alvo:

- possui greeting custom (`generate-*-greeting.*`)
- usa runtime ou contexto ativo em `.aiox/squad-runtime/`
- depende de bootstrap, readiness, blockers ou handoffs
- sofre de ambiguidade sobre "qual e o proximo passo?"

Nao use esta task para agentes simples que so consomem o greeting generico da `.aiox-core`.

---

## Workflow

### Step 1: Locate Greeting Script

```bash
# Find greeting scripts for the target squad
ls squads/{squad}/scripts/generate-*-greeting.*
```

Record the file path. If none found, trigger VETO-NA-001.

### Step 2: Locate Context Sources

Search for context-loading infrastructure:

```yaml
discovery:
  greeting_script: "squads/{squad}/scripts/generate-*-greeting.*"
  context_loader: "load-context.*"
  runtime_resolver: "runtime-paths.*"
  context_writer: "set-active-context.*"
  runtime_files:
    - ".aiox/squad-runtime/{namespace}/.../session-context.yaml"
    - ".aiox/squad-runtime/{namespace}/.../state.json|state.yaml"
```

If no context sources found, trigger VETO-NA-002.

### Step 3: Extract Existing Commands

Map all canonical commands the squad exposes:

- Commands from `config.yaml` activation shortcuts
- Commands from agent files
- Commands from task files

### Step 4: Identify User Friction Points

Analyze the greeting script to determine:

- How context is currently read
- Which status/readiness/blockers already exist
- Where the user typically gets stuck (no clear next step)

---

## Output Contract

```yaml
next_action_discovery:
  squad_name: "{squad_name}"
  greeting_script: "{path}"
  context_sources:
    context_loader: "{path|null}"
    runtime_resolver: "{path|null}"
    context_writer: "{path|null}"
    runtime_files: []
  canonical_commands: []
  existing_status_signals:
    readiness: "{present|absent}"
    blockers: "{present|absent}"
    handoffs: "{present|absent}"
  user_friction_points:
    - "{description of where user gets stuck}"
  veto_check:
    VETO_NA_001: "PASS|FAIL"
    VETO_NA_002: "PASS|FAIL"
```

---

## Completion Criteria

- [ ] Greeting script located and path recorded
- [ ] Context sources mapped (loader, resolver, writer, runtime files)
- [ ] Canonical commands extracted from config/agents/tasks
- [ ] User friction points identified from greeting analysis
- [ ] Discovery map YAML output generated

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `next-action-gap-map.md` |
| **Trigger** | Discovery complete |
| **Artifact** | `next_action_discovery` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of next-action.md_

## Acceptance Criteria

- [ ] All structural sources mapped with zero inference
