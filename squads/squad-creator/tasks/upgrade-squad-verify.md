# Task: Verify Upgrade Integrity

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-verify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: upgrade-squad-verify
name: "Verify Upgrade Integrity"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Re-validate squad after upgrades, compare before/after scores, generate upgrade report, rollback if needed"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::upgrade_squad_verify
Output: artifact::upgrade_squad_verify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Verify post-upgrade squad integrity by re-running validation, comparing scores, and generating the final upgrade report. If the upgrade made things worse, provide rollback instructions.

## Prerequisites

- Completed `upgrade-squad-apply` output (upgrade log)
- Backups available in `squads/{squad_name}/.backup/`

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Name of upgraded squad |
| `upgrade_log` | object | Yes | Output from `upgrade-squad-apply` |
| `before_score` | float | Yes | Score from gap analysis before upgrades |

## Workflow

### Step 1: Re-run Validation

Execute `*validate-squad {squad_name}` (or equivalent structural checks from `upgrade-squad-gap`) on the upgraded squad to produce an after-score.

### Step 2: Compare Before/After

```yaml
comparison:
  before_score: "X.X/10"
  after_score: "Y.Y/10"
  improvement: "+Z.Z points"
  status: "IMPROVED | UNCHANGED | DEGRADED"
  blocking_before: N
  blocking_after: N
  blocking_resolved: N
```

**Status rules:**
- IMPROVED: after_score > before_score
- UNCHANGED: after_score == before_score
- DEGRADED: after_score < before_score (trigger rollback advisory)

### Step 3: Generate Upgrade Report

```yaml
upgrade_report:
  header:
    squad: "{name}"
    upgrade_date: "{date}"
    upgrade_type: "STRUCTURAL"
    upgraded_by: "Squad Architect"
  summary:
    before_score: "X.X/10"
    after_score: "Y.Y/10"
    improvement: "+Z.Z points"
    status: "PASS | NEEDS_MORE_WORK"
  changes_made:
    total: N
    by_type: { structural: N, formatting: N, placeholder: N }
    by_priority: { critical: N, high: N, medium: N, low: N }
  components_upgraded:
    - file: "{path}"
      before: "X.X/10"
      after: "Y.Y/10"
      changes: ["description"]
  remaining_todos:
    structural:
      - file: "{path}"
        todo: "Fill in TODO placeholders"
    qualitative:
      - file: "{path}"
        todo: "voice_dna empty -- use squad-creator-pro"
  recommendations:
    - "Fill in all TODO placeholders in upgraded files"
    - "For qualitative upgrades, use squad-creator-pro *upgrade-squad"
    - "Schedule follow-up validation in 1 week"
  backups:
    location: "squads/{squad}/.backup/"
    files: N
    restore_command: "cp .backup/{file}.bak {file}"
```

Save report to `squads/{squad_name}/docs/upgrade-report-{date}.md`.

### Step 4: Rollback Advisory (if DEGRADED)

If status is DEGRADED:
1. List files that worsened
2. Provide per-file restore commands: `cp .backup/{file}.bak {file}`
3. Recommend re-running gap analysis after rollback

## Output

| Output | Format | Location |
|--------|--------|----------|
| Upgrade Report | Markdown | `{squad}/docs/upgrade-report-{date}.md` |
| Console Summary | Text | Displayed to user |

**Console summary format:**

```
UPGRADE REPORT: {squad_name}
Type: STRUCTURAL

Before: X.X/10  |  After: Y.Y/10  |  Improvement: +Z.Z

Changes: N applied, N failed
Blocking issues resolved: N of M

Status: PASS | NEEDS_MORE_WORK

Remaining TODOs: N structural, N qualitative
Report saved: squads/{squad}/docs/upgrade-report-{date}.md
```

## Acceptance Criteria

- [ ] After-score calculated from fresh validation run
- [ ] Before/after comparison is accurate
- [ ] Upgrade report saved to `docs/` with all sections populated
- [ ] Degraded status triggers rollback advisory with restore commands
- [ ] Remaining TODOs clearly separate structural from qualitative items
- [ ] Report meets completion criteria: after >= before + 1.0 for meaningful improvement

## Veto Conditions

```yaml
veto_conditions: []
```

## Related Documents

| Reference | File |
|-----------|------|
| Previous task | `tasks/upgrade-squad-apply.md` |
| Parent orchestrator | `tasks/upgrade-squad.md` |
| Validate Squad | `tasks/validate-squad.md` |
| Quality Dimensions | `data/quality-dimensions-framework.md` |
| Tier System | `data/tier-system-framework.md` |
