# Task: Apply Structural Upgrades

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-apply` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: upgrade-squad-apply
name: "Apply Structural Upgrades"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Execute approved upgrade plan: backup, apply structural fixes, validate each change, log results"
accountability:
  human: squad-operator
  scope: full
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::upgrade_squad_apply
Output: artifact::upgrade_squad_apply
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Apply STRUCTURAL fixes from the approved upgrade plan. Adds missing fields, fixes format compliance, inserts required sections with placeholder content. Does NOT generate qualitative content (voice DNA, output examples, thinking DNA).

> For qualitative upgrades, use squad-creator-pro `*upgrade-squad`.

## Prerequisites

- Approved `upgrade-squad-plan` output (upgrade plan with selected phases)
- Dry-run completed if VETO-UPGRADE-001 applies

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `upgrade_plan` | object | Yes | Approved plan from `upgrade-squad-plan` |
| `selected_phases` | array | Yes | Phases approved for execution |
| `dry_run` | bool | No | Preview changes without applying |

## Workflow

### Step 1: Pre-Apply Validation

- Verify all target files still exist on disk
- Confirm no concurrent modifications since inventory
- If `dry_run=true`, execute all steps but write nothing -- report what would change

### Step 2: Backup Originals

For each file to be modified:
- Copy to `squads/{squad_name}/.backup/{filename}.{timestamp}.bak`
- Verify backup was written successfully

### Step 3: Apply Auto-Applicable Upgrades

Execute in order of the approved phases. For each component:

**Agent structural additions:**

| Upgrade | When | Action |
|---------|------|--------|
| Add ACTIVATION-NOTICE | Missing at top of file | Insert standard notice |
| Add IDE-FILE-RESOLUTION | Missing section | Insert with base_path for squad |
| Add activation-instructions | Missing section | Insert standard 5-step block |
| Add agent identity fields | Missing agent.name/id/title/whenToUse | Insert with TODO placeholders |
| Add persona section | Missing | Insert with TODO for role and style |
| Add commands section | Missing *help/*exit | Insert standard commands block |
| Add empty voice_dna | Missing section | Insert TODO placeholder structure |
| Add empty output_examples | Missing section | Insert TODO placeholder structure |

**Task structural additions:**

| Upgrade | When | Action |
|---------|------|--------|
| Add missing fields | Required field absent | Insert with sensible defaults |
| Fix execution_type | Invalid enum value | Set to "Agent" (default) |
| Convert to array | input/output is string | Wrap: `"item"` becomes `["item"]` |

**File creation:**

| Upgrade | When | Action |
|---------|------|--------|
| Create README.md | Missing | Minimal README from config.yaml |
| Create CHANGELOG.md | Missing | Initial entry with current date |

### Step 4: Validate Each Change

After each file modification:
- Re-run the relevant structural checks from `upgrade-squad-gap`
- Confirm the targeted gaps are resolved
- If validation fails, restore from backup and log failure

### Step 5: Log All Changes

```yaml
upgrade_log:
  entries:
    - file: "{filename}"
      upgrade_id: "{S-AGT-001}"
      timestamp: "{ISO}"
      status: "applied | failed | skipped"
      type: "structural"
      notes: "{any issues}"
  summary:
    applied: N
    failed: N
    skipped: N
    backups_created: N
```

## Output

| Output | Format | Location |
|--------|--------|----------|
| Upgrade Log | YAML | Passed to next task (`upgrade-squad-verify`) |
| Backups | Files | `squads/{squad_name}/.backup/` |
| Console Summary | Text | Displayed to user |

**Console summary format:**

```
STRUCTURAL UPGRADES APPLIED

Phase 1 Complete:
  [done] agents/{agent}.md - Added loader structure
  [fail] tasks/{task}.md - Validation failed, restored from backup

Changes Applied: N
Changes Failed: N
Backups Created: N

NOTE: Placeholder sections marked with TODO require qualitative content.
Use squad-creator-pro *upgrade-squad for voice DNA generation.
```

## Acceptance Criteria

- [ ] Every modified file has a backup in `.backup/`
- [ ] Each applied change passes re-validation
- [ ] Failed changes are restored from backup automatically
- [ ] Upgrade log records every action with status
- [ ] Dry-run mode produces report without modifying any files
- [ ] TODO placeholders clearly indicate what needs qualitative content

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-UPGRADE-001"
    condition: "No dry-run executed with generated diff against target squad"
    trigger: "Before applying any structural mutation"
    block_behavior: "BLOCK upgrade execution; run dry-run and produce diff first"

  - id: "VETO-UPGRADE-002"
    condition: "Dry-run produced critical blockers not acknowledged"
    trigger: "Before applying any structural mutation"
    block_behavior: "BLOCK apply step until blockers resolved or explicitly accepted"
```

## Related Documents

| Reference | File |
|-----------|------|
| Previous task | `tasks/upgrade-squad-plan.md` |
| Next task | `tasks/upgrade-squad-verify.md` |
| Agent Quality Gate | `checklists/agent-quality-gate.md` |
| Task Anatomy | `checklists/task-anatomy-checklist.md` |
