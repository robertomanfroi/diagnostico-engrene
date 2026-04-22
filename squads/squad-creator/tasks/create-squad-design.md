# Task: Squad Design — Architecture & Scaffold

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad-design` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-squad-design
name: "Squad Design & Scaffold"
category: squad-creation
agent: squad-chief
elicit: true
autonomous: false
description: "Define tier structure, plan agent relationships and handoffs, design quality gates, then create the physical directory structure and initial files."
accountability:
  human: squad-operator
  scope: full
domain: Strategic
merged_from:
  - create-squad-architecture v1.0.0
  - create-squad-scaffold v1.0.0

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::create_squad_design
Output: artifact::create_squad_design
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transform the agent roster from discovery into a complete architectural blueprint with tier assignments, handoff maps, agent synergies/conflicts, and quality gates -- then materialize that architecture into the physical directory structure and initial files. The scaffold is the direct expression of the architecture; separating them was artificial.

## Prerequisites

- [ ] `create-squad-discover` completed successfully (discover output available)
- [ ] Agent roster with tier suggestions defined
- [ ] `data/tier-system-framework.md` loaded
- [ ] `data/decision-heuristics-framework.md` loaded
- [ ] Write permissions for `squads/` directory
- [ ] Templates available: `templates/config-tmpl.yaml`

## Inputs

```yaml
inputs:
  discover_output:
    type: object
    required: true
    description: "Output from create-squad-discover"
    fields: [viability_score, decision, squad_name, entry_agent, slash_prefix, pattern_prefix, mode, squad_type, template_approach, agent_roster, total_agents_planned]
  squad_name:
    type: string
    required: true
  pack_title:
    type: string
    required: true
  entry_agent:
    type: string
    required: true
  version:
    type: string
    required: true
    default: "1.0.0"
  author:
    type: string
    required: true
  mode:
    type: enum
    required: true
    description: '"incremental" or "yolo"'
```

## Workflow / Steps

### Step 2.1: Define Tier Structure

**Apply: tier-system-framework.md**

```yaml
tier_structure_design:
  orchestrator:
    purpose: "Coordinates all tiers, routes requests"
    agent_id: "{squad_name}-chief"

  tier_0_diagnosis:
    purpose: "First contact, analysis, classification"
    agents: "From roster where tier == 0"
    required: true

  tier_1_masters:
    purpose: "Primary experts with core execution capability"
    agents: "From roster where tier == 1"

  tier_2_systematizers:
    purpose: "Framework creators and methodology agents"
    agents: "From roster where tier == 2"

  tier_3_specialists:
    purpose: "Specific format/channel experts"
    agents: "From roster where tier == 3"

  tools:
    purpose: "Validation, checklists, calculators"
    examples: ["quality-checker", "compliance-validator"]
```

### Step 2.2: Plan Agent Relationships

```yaml
agent_relationships:
  handoff_map:
    - from: "orchestrator"
      to: "tier_0_agents"
      when: "New request arrives"

    - from: "tier_0_agents"
      to: "tier_1_agents"
      when: "Diagnosis complete, execution needed"

  synergies:
    - agents: ["diagnosis-agent", "master-agent"]
      pattern: "Diagnosis feeds master context"

  conflicts:
    - agents: ["aggressive-style", "conservative-style"]
      reason: "Contradictory approaches"
```

### Step 2.3: Design Quality Gates

```yaml
quality_gates_design:
  gates:
    - id: "QG-001"
      name: "Request Classification"
      transition: "Input -> Tier 0"
      type: "routing"
      criteria: "Request type identified"

    - id: "QG-002"
      name: "Diagnosis Complete"
      transition: "Tier 0 -> Tier 1"
      type: "blocking"
      criteria: "Analysis approved, requirements clear"

    - id: "QG-003"
      name: "Draft Review"
      transition: "Execution -> Output"
      type: "blocking"
      criteria: "Quality checklist passed"

  escalation_paths:
    - on_failure: "Return to previous tier with feedback"
    - on_repeated_failure: "Escalate to human review"
```

### Step 3.0: Verify No Existing Directory

```yaml
verify_no_collision:
  check: "squads/{squad_name}/ does NOT exist"
  on_exists:
    action: "HALT -- trigger VETO-SQD-001"
    prompt: "Squad directory already exists. Overwrite? (yes/no)"
    on_confirm: "Remove existing and proceed"
    on_deny: "Abort scaffold"
```

### Step 3.1: Create Directory Structure

```yaml
create_directories:
  base: "squads/{squad_name}/"
  subdirectories:
    - agents/
    - tasks/
    - workflows/
    - templates/
    - checklists/
    - data/
    - docs/
```

### Step 3.1.1: Annotate Reasoning Tiers (Conditional)

**[STORY-109.1] AC8 -- Only when model_strategy.enabled is true in the squad config.**

When the squad's config.yaml includes `model_strategy.enabled: true`, annotate each
phase in the tier_structure with a `reasoning_tier` using the verb-pattern heuristic:

```yaml
reasoning_tier_annotation:
  condition: "model_strategy.enabled == true in config.yaml"
  heuristic: "verb-pattern"
  verb_patterns:
    planning:
      - discover
      - research
      - design
      - plan
      - analyze
    implementation:
      - generate
      - create
      - build
      - render
      - scaffold
    verification:
      - validate
      - check
      - verify
      - qa
      - test
  default_tier: "implementation"
  application: |
    For each phase in the tier structure, examine the primary verb
    in the phase name or task names. Classify the phase as:
    - planning: if primary verb matches planning_verbs
    - verification: if primary verb matches verification_verbs
    - implementation: otherwise (default)
    Annotate the phase with reasoning_tier field.
```

When `model_strategy.enabled` is false or absent, skip this step entirely.

### Step 3.2: Create Initial Files

```yaml
create_initial_files:
  config_yaml:
    source: "templates/config-tmpl.yaml"
    target: "squads/{squad_name}/config.yaml"
    interpolate:
      - pack.name: "{squad_name}"
      - pack.version: "{version}"
      - pack.description: "{purpose}"
      - pack.icon: "determined from domain"
      - entry_agent: "{entry_agent}"
      - agents: "from tier_structure"
      - capabilities: "from use_cases"
      - activation.shortcuts: "/{squad_name}:{entry_agent}"

  readme_md:
    target: "squads/{squad_name}/README.md"
    content: "Placeholder -- will be completed in create-squad-build"
    sections:
      - "# {pack_title}"
      - "## Overview"
      - "## Agents"
      - "## Workflows"
      - "## Tasks"
      - "## Usage"
```

### Step 3.3: Initialize Runtime State

```yaml
init_runtime:
  state_file: ".aiox/squad-runtime/create-squad/{squad_name}/state.json"
  initial_state:
    squad_name: "{squad_name}"
    phase: "design_complete"
    created_at: "{timestamp}"
    mode: "{mode}"
    phases_completed: ["discover", "design"]
    phases_remaining: ["build", "validate", "publish"]
```

## Output

```yaml
design_output:
  # Architecture outputs
  tier_structure:
    orchestrator: "{squad}-chief"
    tier_0: ["{diagnosis-agent-1}", "{diagnosis-agent-2}"]
    tier_1: ["{master-agent-1}", "{master-agent-2}"]
    tier_2: ["{systematizer-1}", "{systematizer-2}"]
    tier_3: ["{specialist-1}", "{specialist-2}"]
    tools: ["{tool-1}", "{tool-2}"]
  quality_gates: "{N}"
  handoffs: "{N}"
  architecture_score: "{score}/10"
  # Scaffold outputs
  base_path: "squads/{squad_name}/"
  directories_created: 7
  files_created:
    - "squads/{squad_name}/config.yaml"
    - "squads/{squad_name}/README.md"
  runtime_state: ".aiox/squad-runtime/create-squad/{squad_name}/state.json"
  artifact_produced:
    artifact_id: squad-config-base
    artifact_template: squads/squad-creator/templates/config-tmpl.yaml
    lifecycle_state: draft
  status: "PASS"
```

## Acceptance Criteria

- [ ] Tier 0 defined with at least one agent
- [ ] Orchestrator agent defined as `{squad_name}-chief`
- [ ] Quality gates >= 3
- [ ] Handoff map complete (all tier transitions covered)
- [ ] Agent synergies and conflicts documented
- [ ] In incremental mode: human approval obtained for architecture
- [ ] Directory `squads/{squad_name}/` exists with all 7 subdirectories
- [ ] `config.yaml` is valid YAML with `entry_agent` field populated
- [ ] `config.yaml` defines `workspace_integration.level` (VETO-SQD-004)
- [ ] `README.md` placeholder created
- [ ] Runtime state file initialized
- [ ] No pre-existing directory was overwritten without confirmation

## Veto Conditions

- **VETO-SQD-001:** Squad directory already exists without user confirmation to overwrite
- **VETO-SQD-004:** `config.yaml` missing `workspace_integration.level` field
- Missing Tier 0 definition
- Missing orchestrator definition
- Fewer than 3 quality gates
- Incomplete handoff map (orphan agents with no incoming/outgoing handoffs)

## Related Documents

- `create-squad.md` (parent composed task)
- `create-squad-discover.md` (previous step)
- `create-squad-build.md` (next step)
- `data/tier-system-framework.md`
- `data/decision-heuristics-framework.md`
- `templates/config-tmpl.yaml`

---

_Task Version: 1.0.0 (merged from: create-squad-architecture v1.0.0 + create-squad-scaffold v1.0.0)_
_Last Updated: 2026-03-27_
