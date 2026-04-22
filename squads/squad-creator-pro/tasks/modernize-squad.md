<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: modernize-squad
  task_name: Modernize Squad
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
  - Governance Compliance Audit
  - Task Atomization
  - Workflow Composition
  - Checklist Coverage
  - State Machine Integrity
  acceptance_criteria:
  - Target squad exists and has a valid `config.yaml
  - Squad-creator-pro is active (pro mode required)
  - Write access to the target squad directory
  - 'Phase 1: config.yaml has all governance fields (artifact_contracts, bu_mapping,
    modes, lifecycle)'
  - 'Phase 2: No task exceeds 500 lines or 5 phases (monoliths atomized)'
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Modernize Squad

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `modernize-squad` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata
```yaml
id: modernize-squad
name: "Modernize Squad"
category: enhancement
agent: squad-chief
elicit: true
autonomous: false
description: "Full modernization pipeline for any squad. Applies 6-phase upgrade: governance compliance, atomization, workflow composition, checklist coverage, state machine integrity, and IP sanitization. Produces a squad that follows all framework standards without exposing methodology internals."
```

## Purpose

Elevate any squad to production-grade standards through a systematic 6-phase modernization pipeline. The process ensures structural atomicity, workflow composition, governance compliance, adequate coverage ratios, and IP protection — without requiring knowledge of the underlying methodology.

This is the canonical path for upgrading legacy squads, onboarding external squads, or hardening squads before distribution.

## Prerequisites

- [ ] Target squad exists and has a valid `config.yaml`
- [ ] Squad-creator-pro is active (pro mode required)
- [ ] Write access to the target squad directory

## Inputs

```yaml
inputs:
  squad_path:
    type: filepath
    required: true
    description: "Path to the squad to modernize (e.g., squads/my-squad)"

  phases:
    type: enum[]
    required: false
    default: all
    options: [all, compliance, atomize, workflows, checklists, state-machines, sanitize]
    description: "Which phases to run. Default: all 6 phases sequentially"

  dry_run:
    type: boolean
    required: false
    default: false
    description: "If true, analyze and report without modifying files"
```

## Workflow / Steps

### Phase 1: Governance Compliance Audit

```
PURPOSE: Ensure config.yaml declares all required governance fields

CHECK:
  1. artifact_contracts[] — at least 1 contract with artifact_id, template_path, lifecycle_states
  2. bu_mapping — business unit mapping declared
  3. supported_modes[] — valid operational modes (CRIAR, RESOLVER, GERENCIAR, ENTENDER, VALIDAR, CONFIGURAR, PLANEJAR, EXPLORAR)
  4. artifact_lifecycle — tracking_enabled, state_persistence, transitions
  5. instance_lifecycle — states declared
  6. journey_log — enabled, template, persistence
  7. squad-io.yaml — inputs, outputs, triggers declared
  8. schemas/ — JSON schemas exist for artifact validation

REMEDIATE:
  - Missing fields: Add with sensible defaults (elicit bu_mapping and supported_modes from user)
  - Missing squad-io.yaml: Generate from config.yaml + agent analysis
  - Missing schemas/: Copy base schemas from squad-creator and extend

OUTPUT: compliance_report.yaml with PASS/FAIL per field + remediation applied
```

### Phase 2: Task Atomization

```
PURPOSE: Decompose monolithic tasks (6+ phases, 500+ lines) into atomic sub-tasks

DETECT:
  1. Scan all tasks/*.md files
  2. Count phases per task (grep for "## PHASE" or "### Phase" or "### Step [0-9]")
  3. Count lines per task
  4. Flag tasks with: phases >= 5 OR lines >= 500

FOR EACH flagged task:
  1. Read the full monolithic task
  2. Map each phase to a single responsibility
  3. Create atomic task file per phase (≤200 lines, Task Anatomy format)
  4. Convert original to stub (≤120 lines) that orchestrates sub-tasks
  5. Preserve original Task ID in stub for retrocompatibility

NAMING: {original-task-name}-{phase-verb}.md
  Examples: validate-squad-preflight.md, create-agent-persona.md

RATIOS TARGET:
  - Each atomic task: 100-200 lines
  - Each stub: 80-120 lines
  - Zero functionality loss (content preserved, only restructured)

OUTPUT: atomization_report.yaml with before/after line counts per task
```

### Phase 3: Workflow Composition

```
PURPOSE: Ensure every orchestrator stub has a corresponding workflow YAML

DETECT:
  1. List all stub tasks (tasks that reference sub-tasks)
  2. List all workflows in workflows/
  3. Find stubs WITHOUT a corresponding workflow

FOR EACH missing workflow:
  1. Read the stub to extract: sub-task sequence, inputs, outputs, checkpoints
  2. Generate workflow YAML following gold standard pattern:
     - workflow header (id, name, version, description, type)
     - agent_mapping with phase_ownership
     - state_machine with states + transitions + wildcard fail
     - sequence with task_ref per phase
  3. Each phase references atomic task via task_ref field

VERIFY:
  - Every task_ref in every workflow resolves to an existing task file
  - Zero generic actions without task_ref

RATIO TARGET: tasks:workflows = 8-12:1

OUTPUT: workflow_composition_report.yaml
```

### Phase 4: Checklist Coverage

```
PURPOSE: Ensure quality gates have corresponding checklists

DETECT:
  1. List all major operations (create-*, validate-*, upgrade-*, install-*)
  2. List all checklists in checklists/
  3. Find operations WITHOUT a corresponding checklist

FOR EACH missing checklist:
  1. Read the operation's workflow and tasks
  2. Extract quality gates, blocking conditions, recommended checks
  3. Generate checklist following squad standard format:
     - YAML metadata block
     - blocking checks (must pass)
     - recommended checks (should pass)
     - scoring table

VERIFY:
  - Framework compliance checks present (fw-artifact-contracts, fw-bu-mapping, fw-supported-modes)
  - No references to methodology internals in check descriptions

RATIO TARGET: tasks:checklists = 5-7:1

OUTPUT: checklist_coverage_report.yaml
```

### Phase 5: State Machine Integrity

```
PURPOSE: Ensure all workflows have formal state machines

DETECT:
  1. Scan all workflows/*.yaml
  2. Check for state_machine block presence
  3. Flag workflows WITHOUT state_machine

FOR EACH flagged workflow:
  1. Read the workflow sequence/phases
  2. Generate state_machine block:
     - states: [init, {all phases}, complete, failed]
     - transitions: phase-to-phase + phase-to-failed + wildcard fail
  3. Add to workflow (preserve existing content)

VERIFY:
  - Every state in sequence exists in state_machine.states
  - No dead-end states (except failed, complete)
  - Wildcard fail transition present (source: "*", dest: failed)
  - No orphan states (defined but never in sequence)

OUTPUT: state_machine_report.yaml
```

### Phase 6: IP Sanitization

```
PURPOSE: Remove all methodology-specific references that enable reverse engineering

SCAN for 6 categories:
  C1: Brand + Version (e.g., "{Name} v3.1")
  C2: Brand + Context (e.g., "{Name} compliance/modes/framework")
  C3: Brand + Principle (e.g., "{Name} Mandamento/principle")
  C4: Check/ID prefixes (e.g., "{name}-v31-*", "{NAME}-XX-NNN")
  C5: Internal path references (e.g., "squads/{name}-squad/data/*")
  C6: Extension references (e.g., "{Name} Extension N: Title")

REPLACE:
  C1 → "governance framework"
  C2 → "governance framework|framework compliance|operational modes"
  C3 → "governance principle"
  C4 → "fw-*" / "FW-XX-NNN"
  C5 → "governance/*" or remove path
  C6 → Just the title

VERIFY: Final grep returns 0 references

EXCEPTIONS: agnosticism_exceptions block in config.yaml (e.g., DNA data in clone agents)

OUTPUT: sanitization_report.yaml
```

## Output

```yaml
outputs:
  primary:
    path: ".aiox/squad-runtime/modernize-squad/{squad_name}/modernization-report.md"
    format: markdown
    description: "Full modernization report with 6 phase results"

  per_phase:
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/compliance_report.yaml"
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/atomization_report.yaml"
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/workflow_composition_report.yaml"
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/checklist_coverage_report.yaml"
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/state_machine_report.yaml"
    - ".aiox/squad-runtime/modernize-squad/{squad_name}/sanitization_report.yaml"

  metadata:
    squad: "{squad_name}"
    phases_run: [1,2,3,4,5,6]
    duration: "N minutes"
    files_created: N
    files_modified: N
    tasks_atomized: N
    workflows_created: N
    checklists_created: N
    state_machines_added: N
    references_sanitized: N
```

## Acceptance Criteria

- [ ] Phase 1: config.yaml has all governance fields (artifact_contracts, bu_mapping, modes, lifecycle)
- [ ] Phase 2: No task exceeds 500 lines or 5 phases (monoliths atomized)
- [ ] Phase 3: Every stub has a corresponding workflow with task_refs
- [ ] Phase 4: tasks:checklists ratio is 5-7:1
- [ ] Phase 5: All workflows have state_machine with wildcard fail
- [ ] Phase 6: Zero methodology references in final scan
- [ ] All phases produce reports
- [ ] Squad functionality preserved (commands still work)

## Veto Conditions

- STOP if target squad has no config.yaml (not a valid squad)
- STOP if atomization would break a task that is currently referenced by an external workflow
- STOP if sanitization would break a cross-reference (ID renamed without updating all refs)
- Phase 6 STOP if any non-exception methodology reference remains after replacement

## Decision Heuristics

```yaml
when_to_run_all_phases:
  - First-time modernization of a legacy squad
  - Pre-distribution hardening
  - Post-migration from external framework

when_to_run_specific_phases:
  - Phase 1 only: Quick governance compliance check
  - Phase 2 only: After adding many new tasks that grew too large
  - Phase 6 only: Before sharing squad externally
  - Phases 1+6: Minimum viable hardening for external use
```

## Related Documents

- `tasks/upgrade-squad.md` — Structural upgrade (subset of modernization)
- `tasks/validate-squad.md` — Validation pipeline (runs after modernization)
- External governance sanitization task — Standalone sanitization reference maintained outside this squad
- `checklists/squad-checklist.md` — Full squad validation checklist
