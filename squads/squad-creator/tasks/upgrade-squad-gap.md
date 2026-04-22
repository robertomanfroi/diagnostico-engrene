# Task: Analyze Structural Gaps

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-gap` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: upgrade-squad-gap
name: "Analyze Structural Gaps"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Compare current squad structure against AIOX standards, score compliance, generate gap report"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::upgrade_squad_gap
Output: artifact::upgrade_squad_gap
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Perform STRUCTURAL-ONLY gap analysis on squad components. Checks format compliance, template adherence, field presence, and schema conformance. Does NOT evaluate qualitative aspects (voice DNA quality, thinking DNA depth, mind-cloning fidelity).

> For qualitative upgrades, use squad-creator-pro `*upgrade-squad`.

## Prerequisites

- Completed `upgrade-squad-inventory` output (component inventory)
- Access to current AIOX structural standards

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `inventory` | object | Yes | Output from `upgrade-squad-inventory` |
| `focus` | enum | No | Limit analysis to component type |

## Workflow

### Step 1: Config.yaml Compliance

Run checks S-CFG-001 through S-CFG-008:

| ID | Check | Weight |
|----|-------|--------|
| S-CFG-001 | `config.yaml` exists | blocking |
| S-CFG-002 | Valid YAML syntax | blocking |
| S-CFG-003 | Required fields: name, version, description, entry_agent | blocking |
| S-CFG-004 | Name uses kebab-case (`^[a-z0-9]+(-[a-z0-9]+)*$`) | blocking |
| S-CFG-005 | Version follows semver (`^\d+\.\d+\.\d+$`) | blocking |
| S-CFG-006 | entry_agent references existing agent file | blocking |
| S-CFG-007 | slashPrefix defined | recommended |
| S-CFG-008 | Agents list matches files in `agents/` directory | recommended |

### Step 2: Agent Template Compliance

For each agent file, run checks S-AGT-001 through S-AGT-015:

| ID | Check | Weight |
|----|-------|--------|
| S-AGT-001 | Has ACTIVATION-NOTICE at top | blocking |
| S-AGT-002 | Has IDE-FILE-RESOLUTION section | blocking |
| S-AGT-003 | Has activation-instructions section | blocking |
| S-AGT-004 | agent.name defined | blocking |
| S-AGT-005 | agent.id defined (kebab-case) | blocking |
| S-AGT-006 | agent.title defined | blocking |
| S-AGT-007 | agent.whenToUse defined (20+ chars) | blocking |
| S-AGT-008 | persona section with role and style | blocking |
| S-AGT-009 | core_principles with 3+ items | blocking |
| S-AGT-010 | commands section with *help and *exit | blocking |
| S-AGT-011 | dependencies section exists | recommended |
| S-AGT-012 | voice_dna section exists (not empty) | recommended |
| S-AGT-013 | output_examples section exists (not empty) | recommended |
| S-AGT-014 | anti_patterns section exists | recommended |
| S-AGT-015 | handoff_to section if downstream agents exist | recommended |

### Step 3: Task Anatomy Compliance

For each task file, run checks S-TSK-001 through S-TSK-008:

| ID | Check | Weight |
|----|-------|--------|
| S-TSK-001 | Has all 8 required fields | blocking |
| S-TSK-002 | task_name follows Verb + Object format | blocking |
| S-TSK-003 | execution_type is valid enum (Human/Agent/Hybrid/Worker) | blocking |
| S-TSK-004 | input is array with 1+ items | blocking |
| S-TSK-005 | output is array with 1+ items | blocking |
| S-TSK-006 | action_items has 3+ concrete steps | recommended |
| S-TSK-007 | acceptance_criteria has 2+ testable criteria | recommended |
| S-TSK-008 | Complex tasks (500+ lines) have checklist reference | recommended |

### Step 4: Workflow Schema Compliance

For each workflow file, run checks S-WFL-001 through S-WFL-007:

| ID | Check | Weight |
|----|-------|--------|
| S-WFL-001 | Valid YAML | blocking |
| S-WFL-002 | Has 3+ phases | blocking |
| S-WFL-003 | Each phase has checkpoint | blocking |
| S-WFL-004 | Outputs flow between phases | blocking |
| S-WFL-005 | Quality gate before final output | blocking |
| S-WFL-006 | Has automation script (if 8+ phases) | recommended |
| S-WFL-007 | Phases numbered sequentially | recommended |

### Step 5: Missing Required Files

Run checks S-FIL-001 through S-FIL-007:

| ID | Check | Weight |
|----|-------|--------|
| S-FIL-001 | config.yaml exists | blocking |
| S-FIL-002 | README.md exists | blocking |
| S-FIL-003 | CHANGELOG.md exists | recommended |
| S-FIL-004 | At least one agent in agents/ | blocking |
| S-FIL-005 | Entry agent file exists | blocking |
| S-FIL-006 | All files referenced in config.yaml exist | blocking |
| S-FIL-007 | 80%+ files referenced in agent dependencies exist | recommended |

### Step 6: Score and Generate Gap Report

**Scoring per category:**
- PASS: All blocking checks pass
- NEEDS_UPGRADE: 1-2 (agents: 1-3) blocking checks fail
- CRITICAL: >2 (agents: >3) blocking checks fail

**Output gap report:**

```yaml
gap_report:
  summary:
    squad: "{name}"
    overall_score: "X.X/10"
    status: "PASS | NEEDS_UPGRADE | CRITICAL"
    analysis_type: "STRUCTURAL ONLY"
    components_analyzed: N
    components_passing: N
    components_needing_upgrade: N
    components_critical: N
  by_category:
    config: { status, gaps: { blocking: [], recommended: [] } }
    agents: { total, passing, needing_upgrade, critical, details: [...] }
    tasks: { total, passing, needing_upgrade, critical, details: [...] }
    workflows: { total, passing, needing_upgrade, critical, details: [...] }
    missing_files: { blocking: [], recommended: [] }
  priority_list:
    critical: [{ component, gaps, effort }]
    high: [{ component, gaps, effort }]
    medium: [{ component, gaps, effort }]
    low: [{ component, gaps, effort }]
```

## Output

| Output | Format | Location |
|--------|--------|----------|
| Gap Report | YAML | Passed to next task + `{squad}/docs/gap-report-{date}.md` |
| Console Summary | Table | Displayed to user |

## Acceptance Criteria

- [ ] All structural checks executed per component type
- [ ] Each gap assigned correct weight (blocking/recommended)
- [ ] Overall score calculated from blocking check pass rate
- [ ] Priority list correctly orders by severity then effort
- [ ] Report explicitly states "STRUCTURAL ONLY" analysis type

## Veto Conditions

```yaml
veto_conditions: []
```

## Related Documents

| Reference | File |
|-----------|------|
| Previous task | `tasks/upgrade-squad-inventory.md` |
| Next task | `tasks/upgrade-squad-plan.md` |
| Agent Quality Gate | `checklists/agent-quality-gate.md` |
| Task Anatomy | `checklists/task-anatomy-checklist.md` |
| Squad Checklist | `checklists/squad-checklist.md` |
