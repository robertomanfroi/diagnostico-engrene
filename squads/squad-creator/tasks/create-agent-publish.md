# Task: Agent Publish — IDE Sync & Core Surface Refresh

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-publish` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent-publish
name: "Agent Publish"
category: agent-creation
agent: squad-chief
elicit: false
autonomous: true
description: "Publica um agent recém-criado nas superfícies operacionais: .aiox-sync.yaml, IDE skills e, se for core/chief, Codex + CLAUDE.md."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_agent_publish
Output: artifact::create_agent_publish
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Fechar o gap pós-criação de agent em squads existentes. Depois de validar e
registrar o agent, esta fase publica as superfícies operacionais necessárias
para uso imediato.

## Prerequisites

- [ ] `create-agent-validate` concluída
- [ ] Agent file existe em `squads/{squad_name}/agents/{agent_id}.md`
- [ ] `config.yaml` do squad parseia sem erro

## Inputs

```yaml
inputs:
  validate_output:
    type: object
    required: true
    description: "Output de create-agent-validate"
  squad_name:
    type: string
    required: true
  agent_id:
    type: string
    required: true
```

## Workflow / Steps

### Step 1: Reconcile `.aiox-sync.yaml`

```bash
python3 squads/squad-creator/scripts/update-aiox-sync-config.py --squad {squad_name}
```

### Step 2: Sync Agent to IDE Surfaces

```bash
python3 squads/squad-creator/scripts/sync-ide-skills.py agent {agent_id} --squad {squad_name}
```

Blocking requirement:
- `.claude/skills/{slashPrefix}/{agent_id}/SKILL.md` exists after sync

### Step 3: Refresh Core Surfaces When Agent Is Entry/Core

Core detection rule:

```yaml
is_core_agent:
  any_of:
    - "agent_id == config.entry_agent"
    - "agent_id endswith '-chief'"
```

If core:
- run `node squads/squad-creator/scripts/sync-chief-codex-skill.js --squad {squad_name}`
- run `python3 squads/squad-creator/scripts/update-claude-command-registry.py`

If not core:
- skip with informational note only

## Output

```yaml
publish_output:
  aiox_sync_updated: true
  ide_sync_completed: true
  slash_skill_published: ".claude/skills/{slashPrefix}/{agent_id}/SKILL.md"
  core_surfaces_updated: "true | skipped"
  status: "PASS"
```

## Acceptance Criteria

- [ ] `.aiox-sync.yaml` reconciled
- [ ] Agent synced to `.claude/skills/`
- [ ] If agent is core/chief, Codex skill refreshed
- [ ] If agent is core/chief, root `CLAUDE.md` registry refreshed

## Veto Conditions

- Agent sync fails
- Agent is core/chief and Codex skill refresh fails
- Agent is core/chief and root `CLAUDE.md` refresh fails

## Related Documents

- `create-agent-validate.md`
- `sync-ide-skills.md`
- `sync-chief-codex-skill.md`

---

_Task Version: 1.0.0_
