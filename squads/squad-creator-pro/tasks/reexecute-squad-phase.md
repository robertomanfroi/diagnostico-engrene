# Task: Reexecute Squad Phase

**Task ID:** reexecute-squad-phase
**Version:** 1.0.0
**Execution Type:** Interactive Hybrid
**Purpose:** Re-run one workflow phase with backup and deterministic rollback path
**Orchestrator:** @squad-chief
**Mode:** Human-confirmed for destructive phase cleanup

## Why

```
Brownfield improvements need safe retries.
Reexecution must preserve recoverability.
```

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Target squad |
| `workflow_id` | string | Yes | Workflow to reexecute |
| `phase_id` | string | Yes | Phase to rerun |
| `reason` | text | Yes | Why rerun is required |

---

## Safety Protocol

1. Snapshot phase inputs/outputs.
2. Commit backup with message: `backup: {squad_name} {workflow_id} {phase_id}`.
3. Show impacted downstream phases.
4. Require explicit confirmation.
5. Clean only phase-scoped artifacts.
6. Reexecute phase task list.
7. Run targeted validation.

---

## Output

```yaml
reexecution_report:
  squad_name: "..."
  workflow_id: "..."
  phase_id: "..."
  backup_ref: "git-commit-sha"
  cleaned_artifacts:
    - "..."
  rerun_status: success | fail
  downstream_impacts:
    - "..."
  rollback_instructions: "git checkout {sha} -- <paths>"
```

---

## Validation

- Backup commit created before cleanup.
- No non-phase artifacts removed.
- Target phase completed with no blocking errors.
