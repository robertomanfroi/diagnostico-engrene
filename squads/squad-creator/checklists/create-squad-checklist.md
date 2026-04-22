# Create Squad Checklist

```yaml
checklist:
  id: create-squad-checklist
  version: 1.0.0
  created: 2026-02-10
  purpose: "Validate complete squad creation meets AIOX standards"
  mode: blocking
  task_reference: tasks/create-squad.md
```

---

## Pre-Creation Requirements

```yaml
pre_creation:
  - id: domain-viable
    check: "Domain has sufficient documented methodologies"
    type: blocking
    validation: "viability_score >= 6"

  - id: use-cases-defined
    check: "3-5 key use cases defined"
    type: blocking
    min: 3
    max: 5

  - id: no-duplicate-squad
    check: "No existing squad with > 80% overlap"
    type: blocking
    validation: "overlap_check returns < 80%"
```

---

## Phase 0: Discovery

```yaml
discovery_checks:
  - id: squad-name-valid
    check: "Squad name is kebab-case"
    type: blocking
    pattern: "^[a-z]+(-[a-z]+)*$"

  - id: slash-prefix-valid
    check: "Slash prefix is camelCase"
    type: blocking
    pattern: "^[a-z]+([A-Z][a-z]+)*$"

  - id: config-created
    check: "config.yaml created with required fields"
    type: blocking
    required_fields: ["name", "version", "author", "entry_agent", "slashPrefix", "workspace_integration.level"]
```

---

## Phase 1: Research

```yaml
research_checks:
  - id: minds-found
    check: "5+ elite minds identified"
    type: blocking
    min: 5

  - id: frameworks-documented
    check: "Each mind has documented frameworks"
    type: blocking
    validation: "frameworks_per_mind >= 1 for all"

  - id: tier-0-covered
    check: "At least 1 mind classified as Tier 0 (diagnostic)"
    type: blocking
    validation: "tier_0_count >= 1"

  - id: use-cases-coverage
    check: "Minds cover 80%+ of use cases"
    type: blocking
    threshold: 80
```

---

## Phase 2: Architecture

```yaml
architecture_checks:
  - id: tier-structure-defined
    check: "Tier structure (0-3) defined"
    type: blocking
    tiers: [0, 1, 2, 3]

  - id: orchestrator-planned
    check: "Orchestrator agent planned"
    type: blocking
    validation: "orchestrator in architecture"

  - id: handoff-map-complete
    check: "Handoff map defines all transitions"
    type: blocking
    validation: "all agents have handoff_to defined"

  - id: quality-gates-defined
    check: "3+ quality gates defined"
    type: blocking
    min: 3
```

---

## Phase 3: Creation

```yaml
creation_checks:
  - id: directory-structure
    check: "All required directories created"
    type: blocking
    directories: ["agents/", "tasks/", "workflows/", "templates/", "checklists/", "data/", "docs/"]

  - id: outputs-bootstrap
    check: "Canonical runtime state exists for the squad creation run"
    type: blocking
    validation: ".aiox/squad-runtime/create-squad/{squad_name}/state.json exists"

  - id: orchestrator-created
    check: "Orchestrator agent file exists"
    type: blocking
    validation: "agents/{squad_name}-chief.md exists"

  - id: tier-0-agents
    check: "At least 1 Tier 0 agent created"
    type: blocking
    min: 1

  - id: agents-pass-quality
    check: "All agents pass SC_AGT_001 quality gate"
    type: blocking
    gate: "SC_AGT_001"

  - id: consistency-patterns
    check: "Squad consistency patterns validated (vocabulary, context gate, edit-first)"
    type: recommended
    validation: "Run squad-consistency-patterns.md checklist — score >= 3/5"
    reference: "checklists/squad-consistency-patterns.md"
    template: "templates/squad-mappings-tmpl.yaml"

  - id: workflows-have-checkpoints
    check: "All workflows have checkpoint definitions"
    type: blocking
    validation: "grep 'checkpoint:' returns match for each workflow"

  - id: workflows-contract-validated
    check: "Every created workflow passes workflow-validator.js in strict mode"
    type: blocking
    validator_source: ".aiox-core/development/scripts/workflow-validator.js"
    validation: "run validate_workflow_contract_single.cjs for each squads/{squad_name}/workflows/*.yaml with --strict --fail-on-warnings"
```

---

## Phase 4: Integration

```yaml
integration_checks:
  - id: workspace-integration-level-defined
    check: "Workspace integration level is explicitly declared"
    type: blocking
    validation: "config.yaml contains workspace_integration.level"

  - id: workspace-integration-level-valid
    check: "Workspace integration level uses canonical enum"
    type: blocking
    allowed: ["none", "read_only", "controlled_runtime_consumer", "workspace_first"]

  - id: workspace-contract-declared
    check: "Workspace contract has rationale/read_paths/write_paths"
    type: blocking
    validation: "workspace_integration.rationale/read_paths/write_paths defined"

  - id: coo-handoff-required-for-workspace-write
    check: "If workspace level is controlled_runtime_consumer or workspace_first, COO handoff is documented"
    type: blocking
    conditional: "workspace_integration.level in [controlled_runtime_consumer, workspace_first]"
    validation: ".aiox/squad-runtime/create-squad/{squad_slug}/workspace-handoff.yaml exists OR workflow docs reference COO handoff"

  - id: c-level-presence-required-for-advanced-workspace-integration
    check: "If workspace level is controlled_runtime_consumer or workspace_first, a workspace governance squad exists in repo (`squads/c-level/`)"
    type: blocking
    conditional: "workspace_integration.level in [controlled_runtime_consumer, workspace_first]"
    validation: "test -d squads/c-level"

  - id: workspace-first-requirements
    check: "If level is workspace_first, bootstrap + essentials validator scripts exist"
    type: blocking
    conditional: "workspace_integration.level == workspace_first"
    validation: "scripts/bootstrap-*-workspace.sh && scripts/validate-*-essentials.sh"

  - id: output-path-governance
    check: "Task outputs classified as HIGH-VALUE canonical go to workspace/, not .aiox/squad-runtime/"
    type: blocking
    validation: |
      For each task file in tasks/:
        1. Read output.path
        2. Classify output: HIGH-VALUE (session context, scores, health, maturity,
           onboarding flows, analytics) vs TRANSIENT (drafts, reports, intermediaries)
        3. HIGH-VALUE outputs MUST point to workspace/businesses/{business}/ paths
        4. TRANSIENT outputs MAY point to .aiox/squad-runtime/{squad}/{business}/ paths
      Heuristics for HIGH-VALUE:
        - Loaded on agent boot (session context)
        - Used as input by other tasks
        - Snapshot of business state (scores, maturity, health)
        - Template preenchido que vira dado canônico
      FAIL if any HIGH-VALUE output points to .aiox/squad-runtime/

  - id: dependencies-wired
    check: "All agent dependencies exist"
    type: blocking
    validation: "all files in dependencies[] exist"

  - id: chief-command-published
    check: "Chief slash skill exists after integration sync"
    type: blocking
    validation: ".claude/skills/*/{entry_agent}/SKILL.md exists"

  - id: chief-codex-skill-published
    check: "Chief Codex skill exists after integration sync"
    type: blocking
    validation: ".codex/skills/{entry_agent}/SKILL.md exists"

  - id: readme-complete
    check: "README.md has all required sections"
    type: blocking
    sections: ["overview", "installation", "quick_start", "agents_list"]

  - id: config-valid
    check: "config.yaml passes YAML lint"
    type: blocking
    validation: "yamllint passes"

  - id: fw-artifact-contracts
    check: "config.yaml declares artifact_contracts[] with at least 1 contract"
    type: blocking
    validation: "config.yaml contains artifact_contracts with artifact_id + template_path + lifecycle_states"

  - id: fw-bu-mapping
    check: "config.yaml declares bu_mapping"
    type: blocking
    validation: "config.yaml contains bu_mapping field"

  - id: fw-supported-modes
    check: "config.yaml declares supported_modes[] with valid operational modes"
    type: blocking
    validation: "supported_modes contains only: CRIAR, RESOLVER, GERENCIAR, ENTENDER, VALIDAR, CONFIGURAR, PLANEJAR, EXPLORAR"

  - id: fw-artifact-lifecycle
    check: "config.yaml declares artifact_lifecycle with tracking_enabled"
    type: recommended
    validation: "artifact_lifecycle.tracking_enabled exists"

  - id: fw-instance-lifecycle
    check: "config.yaml declares instance_lifecycle with states"
    type: recommended
    validation: "instance_lifecycle.states exists"

  - id: fw-journey-log
    check: "config.yaml declares journey_log with enabled flag"
    type: recommended
    validation: "journey_log.enabled exists"

  - id: fw-squad-io
    check: "squad-io.yaml exists with inputs, outputs, triggers"
    type: recommended
    validation: "squad-io.yaml exists with inputs[] + outputs[] + triggers[]"
```

---

## Phase 5: Validation

```yaml
validation_checks:
  - id: checklist-pass
    check: "Squad passes squad-checklist.md"
    type: blocking
    checklist: "checklists/squad-checklist.md"

  - id: quality-score
    check: "Quality dimensions score >= 7.0"
    type: blocking
    threshold: 7.0

  - id: no-blocking-issues
    check: "No blocking issues remain"
    type: blocking
    validation: "blocking_issues_count == 0"
```

---

## Final Metrics

```yaml
final_metrics:
  - agents_created: "count"
  - total_lines: "sum across all files"
  - quality_score: "average of all components"
  - use_cases_coverage: "percentage"
```

---

## Scoring

| Score | Result | Action |
|-------|--------|--------|
| 100% Blocking | PASS | Squad ready for use |
| 90%+ Blocking | CONDITIONAL | Document gaps, usable with warnings |
| <90% Blocking | FAIL | Fix issues before handoff |

---

**Created:** 2026-02-10
**Task Reference:** tasks/create-squad.md
