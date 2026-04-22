# Task: Upgrade Squad (Orchestrator)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: upgrade-squad
name: "Upgrade Squad"
category: upgrade
agent: squad-chief
elicit: true
autonomous: false
description: "Orchestrator -- delegates to 5 atomic tasks to upgrade squads to current AIOX structural standards"
accountability:
  human: squad-operator
  scope: full
domain: Strategic

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::upgrade_squad
Output: artifact::upgrade_squad
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Upgrade existing squads to current AIOX structural standards with gap analysis and automated improvements. This orchestrator delegates to atomic subtasks -- it does not execute upgrade logic directly.

For qualitative upgrades (voice DNA quality, thinking DNA gaps), use squad-creator-pro `*upgrade-squad`.

## PRO Detection

> At execution time, check if `squads/squad-creator-pro/workflows/wf-brownfield-upgrade-squad.yaml` exists.
> If YES and pro mode is active -- delegate to pro workflow override.
> If NO -- continue with this base version.

## Inputs

| Parameter | Type | Required | Description | Example |
|-----------|------|----------|-------------|---------|
| `squad_name` | string | Yes | Name of squad to upgrade | `"copy"`, `"legal"` |
| `mode` | enum | No | `audit`, `plan`, `execute`, `auto` | `execute` |
| `focus` | enum | No | `agents`, `tasks`, `workflows`, `all` | `all` |
| `dry_run` | bool | No | Preview changes without applying | `true` |

## Pipeline

```
[upgrade-squad-inventory] --> [upgrade-squad-gap] --> [upgrade-squad-plan]
                                                          |
                                              (mode=audit stops here)
                                                          |
                                                  [upgrade-squad-apply] --> [upgrade-squad-verify]
```

| Phase | Task ID | Stops at mode |
|-------|---------|---------------|
| 0. Inventory | `upgrade-squad-inventory` | -- |
| 1. Gap Analysis | `upgrade-squad-gap` | `audit` |
| 2. Plan | `upgrade-squad-plan` | `plan` |
| 3. Apply | `upgrade-squad-apply` | -- |
| 4. Verify | `upgrade-squad-verify` | -- |

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-UPGRADE-001"
    condition: "No dry-run executed with generated diff against target squad"
    trigger: "Before Phase 3 (upgrade-squad-apply)"
    block_behavior: "BLOCK upgrade execution; run dry-run and produce diff first"

  - id: "VETO-UPGRADE-002"
    condition: "Dry-run produced critical blockers not acknowledged"
    trigger: "Before applying any structural mutation"
    block_behavior: "BLOCK apply step until blockers are resolved or explicitly accepted"
```

## Usage

```bash
@squad-chief
*upgrade-squad copy --mode=audit        # Inventory + gap report only
*upgrade-squad copy --mode=plan         # + upgrade plan
*upgrade-squad copy --mode=execute      # + apply with confirmations
*upgrade-squad copy --mode=auto         # Full autonomous execution
*upgrade-squad copy --dry-run           # Preview all changes
*upgrade-squad copy --focus=agents      # Scope to agents only
```

## Anti-Patterns

- Upgrade without backup (use `upgrade-squad-apply` which enforces backups)
- Auto-apply qualitative content changes (structural only)
- Skip verification after upgrades (always run `upgrade-squad-verify`)
- Attempt voice DNA generation (delegate to squad-creator-pro)

## Completion Criteria

- All critical structural gaps resolved (or documented as exceptions)
- After score >= Before score + 1.0 (meaningful improvement)
- No blocking structural checks failing
- Upgrade report generated
- Backups verified

## Related Documents

| Subtask | File |
|---------|------|
| Phase 0: Inventory | `tasks/upgrade-squad-inventory.md` |
| Phase 1: Gap Analysis | `tasks/upgrade-squad-gap.md` |
| Phase 2: Plan | `tasks/upgrade-squad-plan.md` |
| Phase 3: Apply | `tasks/upgrade-squad-apply.md` |
| Phase 4: Verify | `tasks/upgrade-squad-verify.md` |

| Reference | File |
|-----------|------|
| Agent Quality Gate | `checklists/agent-quality-gate.md` |
| Task Anatomy | `checklists/task-anatomy-checklist.md` |
| Squad Checklist | `checklists/squad-checklist.md` |
| Quality Dimensions | `data/quality-dimensions-framework.md` |
| Tier System | `data/tier-system-framework.md` |
