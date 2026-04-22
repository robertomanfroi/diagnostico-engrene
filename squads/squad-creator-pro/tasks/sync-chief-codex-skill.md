<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: sync-chief-codex-skill
  task_name: /sync-chief-codex-skill Task
  status: pending
  responsible_executor: Worker
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - All veto conditions checked and none triggered
  - 'Output artifact produced: Completed sync-chief-codex-skill output artifact'
  - Task output validated against quality standards
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


# /sync-chief-codex-skill Task

**Task ID:** sync-chief-codex-skill
**Execution Type:** `Worker` (deterministic file generation)
**Model:** Haiku
**Haiku Eligible:** YES
**Worker Script:** `scripts/sync-chief-codex-skill.js`

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-SCS-001 | Squad config.yaml must exist and be parseable before generating skill file | Validate squads/{squad_name}/config.yaml exists and YAML parses without error | VETO - BLOCK. Fix or create config.yaml before attempting skill sync. |
| VETO-SCS-002 | Chief agent must be resolvable from config before writing skill file | Verify chief resolution chain (entry_agent, squad.entry_agent, tier_system.orchestrator, agents[]) returns a valid agent ID | VETO - BLOCK. Define entry_agent or orchestrator in config.yaml before proceeding. |
| VETO-SCS-003 | Existing SKILL.md at target path must be backed up before overwrite | Check if .codex/skills/{chief_id}/SKILL.md already exists | VETO - BLOCK. Create backup of existing skill file before generating new version. |

---

When this task is used, execute:

```bash
node squads/squad-creator-pro/scripts/sync-chief-codex-skill.js --squad {squad_name}
```

## Purpose

Generate or update the Codex skill for the squad chief so the orchestrator is immediately activatable in Codex after squad creation.

## Inputs

- `squad_name` (required): Squad directory name under `squads/`.

## Deterministic Behavior

1. Read `squads/{squad_name}/config.yaml`.
2. Resolve chief id via (priority):
   - `entry_agent`
   - `squad.entry_agent`
   - `tier_system.orchestrator`
   - first `agents[].id` that is orchestrator or ends with `-chief`
3. Read chief agent file in `squads/{squad_name}/agents/`.
4. Extract command set from chief YAML block.
5. Write `.codex/skills/{chief_id}/SKILL.md`.

## Required Output

- `.codex/skills/{chief_id}/SKILL.md`

## Blocking Rule

If the chief cannot be resolved or the chief file is missing, fail the task and block final handoff.

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed sync-chief-codex-skill output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Completed sync-chief-codex-skill output artifact
- [ ] Task output validated against quality standards
