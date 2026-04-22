# Task: Generate Upgrade Plan

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-plan` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: upgrade-squad-plan
name: "Generate Upgrade Plan"
category: upgrade
agent: squad-chief
elicit: true
autonomous: false
description: "Prioritize gaps, estimate effort, generate phased upgrade plan, present for approval"
accountability:
  human: squad-operator
  scope: full
domain: Strategic

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::upgrade_squad_plan
Output: artifact::upgrade_squad_plan
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transform the gap report into a prioritized, phased upgrade plan with effort estimates. Present the plan for user approval before any modifications are made. In `auto` mode, approval is implicit.

## Prerequisites

- Completed `upgrade-squad-gap` output (gap report with priority list)

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `gap_report` | object | Yes | Output from `upgrade-squad-gap` |
| `mode` | enum | No | `plan` (default) or `auto` |

## Workflow

### Step 1: Prioritize Upgrades

Apply prioritization rules:

| Priority | Criteria | Action |
|----------|----------|--------|
| Critical | Blocking structural checks failing; component unusable | Must fix before production-ready |
| High | Missing required sections; template non-compliant | Should fix in this upgrade cycle |
| Medium | Recommended checks failing; score below 7.0 | Fix if time permits |
| Low | Minor structural improvements; format consistency | Optional polish |

### Step 2: Estimate Effort

For each component requiring upgrade, estimate effort based on gap count:
- 1 gap: ~15m
- 2-3 gaps: ~30m
- 4-5 gaps: ~45m
- 6+ gaps: ~1h+

Mark each upgrade as `auto_applicable: true/false` based on whether it can be safely automated (structural additions only, no qualitative content generation).

### Step 3: Generate Phased Plan

```yaml
upgrade_plan:
  squad: "{name}"
  generated: "{timestamp}"
  total_components: N
  components_to_upgrade: N
  estimated_effort: "X-Yh"
  upgrade_type: "STRUCTURAL"
  phases:
    - phase: 1
      name: "Critical Structural Fixes"
      components:
        - file: "{path}"
          upgrades: ["description of each fix"]
          effort: "Xm"
          auto_applicable: true/false
    - phase: 2
      name: "Required Sections"
      components: [...]
    - phase: 3
      name: "Structural Polish"
      components: [...]
```

### Step 4: Present Plan for Approval (elicit)

If mode is not `auto`, present the plan and ask:

```
UPGRADE PLAN: {squad_name}
Type: STRUCTURAL UPGRADES ONLY

Phase 1: Critical Structural Fixes (Est: Xh)
  +-- {file} [AUTO] - {description}

Phase 2: Required Sections (Est: Xh)
  +-- {file} [AUTO] - {description}

Phase 3: Structural Polish (Est: Xm)
  +-- {file} [AUTO] - {description}

Options:
1. Execute Phase 1 only (critical structural fixes)
2. Execute Phases 1-2 (with mandatory sections)
3. Execute all phases
4. Export plan and exit
5. Cancel

Which option? [1-5]:
```

## Output

| Output | Format | Location |
|--------|--------|----------|
| Upgrade Plan | YAML | Passed to next task (`upgrade-squad-apply`) |
| User Decision | enum | Phase scope selected (1/1-2/all/export/cancel) |

## Acceptance Criteria

- [ ] All gaps from the report appear in exactly one phase
- [ ] Phases ordered by priority: critical, high, medium, low
- [ ] Each component has effort estimate and auto_applicable flag
- [ ] Plan presented to user with clear options (unless auto mode)
- [ ] User selection correctly scopes which phases to execute

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-PLAN-001"
    condition: "Gap report is empty (no gaps found)"
    trigger: "Before Step 1"
    block_behavior: "SKIP plan generation, report squad is fully compliant"
```

## Related Documents

| Reference | File |
|-----------|------|
| Previous task | `tasks/upgrade-squad-gap.md` |
| Next task | `tasks/upgrade-squad-apply.md` |
| Quality Dimensions | `data/quality-dimensions-framework.md` |
