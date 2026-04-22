# Task: Squad Publish — Activation Surfaces & Smoke Test

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad-publish` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-squad-publish
name: "Squad Publish & Smoke Test"
category: squad-creation
agent: squad-chief
elicit: false
autonomous: true
description: "Publica superfícies de ativação (aiox-sync, IDE skills, Codex skill, CLAUDE.md registry) e verifica operacionalmente que o squad funciona via smoke test."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
merged_from:
  - create-squad-publish v1.0.0
  - create-squad-smoke-test v1.0.0

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_squad_publish
Output: artifact::create_squad_publish
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Fechar o gap entre "squad criado no disco" e "squad realmente ativavel". Publica as superficies operacionais obrigatorias e verifica que o squad e funcional com um smoke test minimo de ponta a ponta. Publicar sem verificar e irresponsavel; verificar sem publicar e impossivel.

## Prerequisites

- [ ] `create-squad-validate` concluida com status PASS
- [ ] `config.yaml` contem `entry_agent` e `slashPrefix`
- [ ] Chief do squad existe em `agents/{entry_agent}.md`
- [ ] Activation surface contract prepared (from build phase)

## Inputs

```yaml
inputs:
  validate_output:
    type: object
    required: true
    description: "Output de create-squad-validate"
    fields: [checklist_pass, quality_score, governance_compliance, status]
  squad_name:
    type: string
    required: true
  entry_agent:
    type: string
    required: true
  slash_prefix:
    type: string
    required: true
  config_path:
    type: file
    required: true
    path: "squads/{squad_name}/config.yaml"
    description: "Squad configuration file"
```

## Workflow / Steps

### Step 1: Reconcile `.aiox-sync.yaml`

```bash
python3 squads/squad-creator/scripts/update-aiox-sync-config.py --squad {squad_name}
```

Expected result:
- `.aiox-sync.yaml` existe no root
- `squad_aliases.{squad_name} = {slash_prefix}`

### Step 2: Publish IDE Skill Surfaces

Run the composed installation flow:

```text
task: install-skills
input:
  squad_name: {squad_name}
```

Blocking requirement:
- `.claude/skills/{slash_prefix}/{entry_agent}/SKILL.md` must exist at the end

### Step 3: Publish Codex Chief Skill

```text
task: sync-chief-codex-skill
input:
  squad_name: {squad_name}
```

Blocking requirement:
- `.codex/skills/{entry_agent}/SKILL.md` must exist

### Step 4: Update Root `CLAUDE.md` Activation Registry

```bash
python3 squads/squad-creator/scripts/update-claude-command-registry.py
```

Expected result:
- root `CLAUDE.md` contains an updated generated registry block
- the new squad activation surface is listed there

### Step 5: Smoke Test — Activate Entry Agent

```yaml
smoke_test_activation:
  action: "Load the entry agent file from squads/{squad_name}/agents/{entry_agent}.md"
  checks:
    - parse: "Agent file is well-formed (has agent.id, persona, commands)"
    - greeting: "Agent responds with a greeting matching greeting_levels"
  pass_criteria: "Agent file loads without parse errors, greeting text present"
```

### Step 6: Smoke Test — Verify *help Command

```yaml
smoke_test_help:
  action: "Simulate *help command against the entry agent definition"
  checks:
    - commands_exist: "Agent has a commands section with at least 1 command defined"
    - command_structure: "Each command has: name, description, visibility"
  pass_criteria: "Commands list is non-empty and well-structured"
```

### Step 7: Smoke Test — Test One Command

```yaml
smoke_test_command:
  action: "Select the first non-help command from the agent's command list"
  checks:
    - task_resolution: "Command has a corresponding task (check dependencies.tasks)"
    - file_exists: "Referenced task file exists on disk"
  pass_criteria: "At least one command resolves to an existing task file"
```

### Step 8: Generate Smoke Test Report

```yaml
smoke_test_report:
  file: ".aiox/squad-runtime/create-squad/{squad_name}/validation/smoke-test-report.md"
  content:
    - test_date: "{timestamp}"
    - squad: "{squad_name}"
    - scenarios:
      - activation: "PASS | FAIL"
      - help_command: "PASS | FAIL"
      - basic_task: "PASS | FAIL"
    - overall_verdict: "PASS (3/3) | FAIL (with details)"
    - activation_command: "@{squad_name}"
```

## Output

```yaml
publish_output:
  # Publish outputs
  aiox_sync_updated: true
  slash_skill_published: ".claude/skills/{slash_prefix}/{entry_agent}/SKILL.md"
  codex_skill_published: ".codex/skills/{entry_agent}/SKILL.md"
  claude_registry_updated: true
  # Smoke test outputs
  smoke_test_verdict: "PASS | FAIL"
  smoke_test_report: ".aiox/squad-runtime/create-squad/{squad_name}/validation/smoke-test-report.md"
  scenarios_passed: "{N}/3"
  status: "PASS"
```

## Acceptance Criteria

- [ ] `.aiox-sync.yaml` created or reconciled
- [ ] IDE sync triggered through `install-skills`
- [ ] Chief slash skill exists in `.claude/skills/{slash_prefix}/{entry_agent}/SKILL.md`
- [ ] Chief Codex skill exists in `.codex/skills/{entry_agent}/SKILL.md`
- [ ] Root `CLAUDE.md` registry updated
- [ ] Entry agent file loads and parses without errors
- [ ] Greeting text is present and matches agent persona
- [ ] *help lists at least 1 command with name and description
- [ ] At least 1 command resolves to an existing task file
- [ ] Smoke test report generated with 3 scenario results
- [ ] Overall verdict is PASS only when all 3 scenarios pass

## Veto Conditions

- Missing `entry_agent` or `slashPrefix`
- Skill surface not published
- Codex chief skill not published
- Root `CLAUDE.md` registry update fails
- Entry agent file does not exist or fails to parse
- config.yaml does not define an entry_agent
- Smoke test passes but no report is generated

## Related Documents

- `create-squad.md` (parent composed task)
- `create-squad-validate.md` (previous step)
- `install-skills.md`
- `sync-chief-codex-skill.md`

---

_Task Version: 2.0.0 (merged from: create-squad-publish v1.0.0 + create-squad-smoke-test v1.0.0)_
_Last Updated: 2026-03-27_
