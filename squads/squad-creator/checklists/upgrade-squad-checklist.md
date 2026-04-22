# Upgrade Squad Checklist

```yaml
checklist:
  id: upgrade-squad-checklist
  version: 1.0.0
  created: 2026-03-26
  purpose: "Validate squad upgrade process from current version to target version"
  mode: blocking
  task_reference: tasks/upgrade-squad.md
```

---

## Pre-Upgrade Inventory

```yaml
inventory_checks:
  - id: current-version-documented
    check: "Current squad version recorded from config.yaml"
    type: blocking
    validation: "config.yaml version field read and logged"

  - id: target-version-defined
    check: "Target version or upgrade scope is clearly defined"
    type: blocking
    validation: "Upgrade target specified (version bump, governance framework compliance, structural fix, etc.)"

  - id: file-inventory-complete
    check: "Full inventory of existing squad files documented"
    type: blocking
    validation: "List of all files in agents/, tasks/, workflows/, templates/, checklists/, data/ recorded"

  - id: agent-count-recorded
    check: "Number of agents, tasks, workflows, and checklists recorded"
    type: blocking
    fields: ["agents_count", "tasks_count", "workflows_count", "checklists_count", "templates_count"]

  - id: config-snapshot-taken
    check: "Current config.yaml contents captured before modification"
    type: blocking
    validation: "config.yaml content saved to pre-upgrade snapshot"
```

---

## Gap Analysis

```yaml
gap_checks:
  - id: gap-analysis-documented
    check: "Gap analysis identifies what is missing relative to target standards"
    type: blocking
    validation: "List of missing fields, files, or sections documented"

  - id: fw-compliance-gaps
    check: "Governance framework compliance gaps identified (artifact_contracts, bu_mapping, supported_modes)"
    type: blocking
    validation: |
      Check config.yaml for:
      - artifact_contracts[] with artifact_id + template_path + lifecycle_states
      - bu_mapping field
      - supported_modes[] with valid operational modes

  - id: structural-gaps
    check: "Missing directories or required files identified"
    type: blocking
    required_dirs: ["agents/", "tasks/", "workflows/", "templates/", "checklists/", "data/"]

  - id: cross-reference-gaps
    check: "Broken internal references identified (agents referencing missing tasks, etc.)"
    type: blocking
    validation: "All handoff_to, task references, template references resolve"

  - id: workspace-integration-gap
    check: "Workspace integration level assessed against current squad capabilities"
    type: recommended
    validation: "workspace_integration.level is declared and rationale is present"
```

---

## Upgrade Plan

```yaml
plan_checks:
  - id: upgrade-plan-exists
    check: "Written upgrade plan lists all changes to be made"
    type: blocking
    validation: "Plan document or section enumerates changes with order of execution"

  - id: plan-has-priorities
    check: "Changes are prioritized (blocking fixes first, then recommended improvements)"
    type: blocking
    validation: "Plan separates blocking items from recommended items"

  - id: plan-reviewed
    check: "Upgrade plan reviewed before execution (human or agent review)"
    type: recommended
    validation: "Plan presented for confirmation before destructive changes"

  - id: breaking-changes-flagged
    check: "Any breaking changes (renamed agents, removed tasks, changed APIs) are flagged"
    type: blocking
    validation: "Breaking changes section exists if applicable, or explicitly states 'none'"
```

---

## Backup

```yaml
backup_checks:
  - id: backup-created
    check: "Pre-upgrade backup of squad directory exists"
    type: blocking
    validation: "git stash or git commit captures current state before modifications"

  - id: backup-is-restorable
    check: "Backup can be restored if upgrade fails"
    type: blocking
    validation: "git log or git stash list confirms recovery point exists"

  - id: config-backup
    check: "config.yaml backed up independently (critical file)"
    type: recommended
    validation: "config.yaml state recoverable from git history"
```

---

## Post-Upgrade Verification

```yaml
verification_checks:
  - id: config-valid-yaml
    check: "Updated config.yaml passes YAML lint"
    type: blocking
    validation: "yamllint returns no errors"

  - id: config-required-fields
    check: "config.yaml retains all required fields after upgrade"
    type: blocking
    required_fields: ["name", "version", "description", "entry_agent"]

  - id: version-bumped
    check: "config.yaml version field incremented appropriately"
    type: blocking
    validation: "New version > old version (semver comparison)"

  - id: entry-agent-activates
    check: "Entry agent activates without errors post-upgrade"
    type: blocking
    validation: "/{squad-name}:{entry-agent} loads successfully"

  - id: all-references-resolve
    check: "All internal cross-references resolve after upgrade"
    type: blocking
    validation: "No broken handoff_to, task, template, or checklist references"

  - id: squad-checklist-passes
    check: "Upgraded squad passes squad-checklist.md Tier 1 (Structure)"
    type: blocking
    checklist: "checklists/squad-checklist.md"

  - id: fw-compliance-complete
    check: "All governance framework required fields present in config.yaml"
    type: blocking
    validation: "artifact_contracts[], bu_mapping, supported_modes[] all present"
```

---

## Regression Detection

```yaml
regression_checks:
  - id: no-agents-lost
    check: "Agent count is equal to or greater than pre-upgrade count"
    type: blocking
    validation: "post_agents_count >= pre_agents_count (unless intentional removal documented)"

  - id: no-tasks-lost
    check: "Task count is equal to or greater than pre-upgrade count"
    type: blocking
    validation: "post_tasks_count >= pre_tasks_count (unless intentional removal documented)"

  - id: no-workflows-broken
    check: "All workflows that existed pre-upgrade still pass contract validation"
    type: blocking
    validation: "workflow-validator.js returns PASS for all existing workflows"

  - id: commands-still-work
    check: "Previously installed IDE skill surfaces still activate correctly"
    type: recommended
    validation: "All slash skill activations that worked before upgrade still work"

  - id: no-orphan-tasks
    check: "Upgrade did not create orphan tasks (unreferenced by any agent or workflow)"
    type: recommended
    validation: "Zero orphan tasks post-upgrade"

  - id: intentional-removals-documented
    check: "If any files were removed, removals are documented with rationale"
    type: blocking
    validation: "Removed files listed in upgrade report with reason"
```

---

## Scoring

| Score | Result | Action |
|-------|--------|--------|
| 100% Blocking | PASS | Upgrade complete and verified |
| 90%+ Blocking | CONDITIONAL | Usable with documented gaps, schedule follow-up |
| <90% Blocking | FAIL | Restore from backup, fix plan, retry |

---

**Created:** 2026-03-26
**Task Reference:** tasks/upgrade-squad.md
