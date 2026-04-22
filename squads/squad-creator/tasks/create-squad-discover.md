# Task: Squad Discovery — Domain Viability & Type Selection

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad-discover` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-squad-discover
name: "Squad Discovery & Type Selection"
category: squad-creation
agent: squad-chief
elicit: true
autonomous: false
description: "Validate domain viability, check existing squads, define squad structure, select squad type from catalog, choose template approach, and map use cases to agent roles."
accountability:
  human: squad-operator
  scope: full
merged_from:
  - create-squad-discover v1.0.0
  - create-squad-select-type v1.0.0

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_squad_discover
Output: artifact::create_squad_discover
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Validate that a proposed squad domain is viable, check for existing squads that may overlap, assess workspace domain alignment, define the basic squad structure (name, prefix, entry agent), select the best squad archetype from `squad-type-definitions.yaml`, choose between operational and expert template approaches, and produce an initial agent roster with tier assignments and use case coverage. Type selection is the natural output of discovery -- once you know the domain, the type follows.

## Prerequisites

- [ ] squad-chief agent is active
- [ ] WebSearch tool available (for domain research)
- [ ] Write permissions for `squads/` directory
- [ ] `data/squad-type-definitions.yaml` exists and is readable
- [ ] `data/tier-system-framework.md` loaded

## Inputs

```yaml
inputs:
  domain:
    type: string
    required: true
    description: "Domain expertise area"
    example: '"copywriting", "legal", "data"'
  purpose:
    type: string
    required: true
    description: "What the squad should accomplish"
    example: '"Create high-converting sales pages"'
  target_user:
    type: string
    required: true
    description: "Who will use this squad"
    example: '"Marketing teams at SaaS companies"'
  use_cases:
    type: list
    required: true
    description: "3-5 key use cases"
    example: '["sales pages", "email sequences", "ads"]'
  mode:
    type: enum
    required: true
    description: '"incremental" or "yolo"'
  squad_name:
    type: string
    required: false
    description: "Override default name"
```

## Workflow / Steps

### Step 0.0: Workspace Domain Awareness

```yaml
workspace_domain_check:
  read_files:
    - "workspace/_system/config.yaml"
    - "workspace/businesses/"

  checks:
    - product_alignment: "Squad serve qual produto em workspace/businesses/{bu}/L3-product/?"
    - provider_overlap: "Squad usa providers ja declarados em workspace.yaml?"

  output:
    workspace_context:
      domain_match: "exact | partial | none"
      related_products: ["list"]
      available_providers: ["list"]
      existing_squads_for_domain: ["list"]

  behavior:
    domain_exists: "Informar ao usuario que o dominio ja tem definicoes no workspace. Squad deve alinhar com entities.yaml e workflows.yaml do dominio."
```

### Step 0.1: Validate Domain Viability

```yaml
domain_viability_check:
  questions:
    - "Is this domain well-documented with established methodologies?"
    - "Do recognized practitioners exist with documented frameworks?"
    - "Can outputs be validated against objective criteria?"
    - "Is there enough depth to warrant a squad (vs single agent)?"

  scoring:
    - documented_methodologies: 0-3
    - recognized_practitioners: 0-3
    - validation_criteria: 0-2
    - complexity_warrants_squad: 0-2

  threshold: 6/10
  veto_conditions:
    - recognized_practitioners < 2 -> "Cannot create quality agents without domain research"
```

**Decision Point:**
```
IF viability_score >= 6:
    -> PROCEED to Step 0.1.1
ELSE IF viability_score >= 4:
    -> WARN: "Domain may not support full squad. Consider single agent."
    -> ASK: "Proceed with limited scope?"
ELSE:
    -> BLOCK: "Domain lacks sufficient documented frameworks"
    -> SUGGEST: "Consider researching domain first or choosing adjacent domain"
```

### Step 0.1.1: Native Scope Gate

```yaml
native_scope_gate:
  trigger:
    workflows_mapped_gte: 10
    agents_needed_gte: 8

  when_triggered:
    action: HALT direct creation
    required_prd: "docs/projects/{domain}/prd.md"

    if_prd_missing_or_invalid:
      response:
        - "Do NOT scaffold partial squad structure"
        - "Return explicit handoff: *plan-squad {domain}"

    if_prd_present:
      response:
        - "Require epic-scoped execution"
        - "Use: *create-squad {domain} --epic=1"
        - "Initialize runtime state before execution"
```

### Step 0.2: Check Existing Squads

```yaml
existing_squad_check:
  search_paths:
    - "squads/{similar_names}/"
    - "squads/*/{domain}*"
    - ".claude/skills/*/{domain}*/SKILL.md"

  analysis:
    - existing_coverage: "What does existing squad cover?"
    - gap_identification: "What's missing?"
    - extension_vs_new: "Extend existing or create new?"

  output:
    decision: "extend" | "create_new" | "abort_duplicate"
    rationale: "..."
```

**Decision Point:**
```
IF existing squad covers 80%+ of use cases:
    -> SUGGEST: "Extend existing squad instead"
    -> IF user confirms: -> GOTO extend-squad workflow
IF partial overlap:
    -> WARN: "Partial overlap detected. Plan for integration."
ELSE:
    -> PROCEED to Step 0.3
```

### Step 0.3: Define Squad Structure

```yaml
pack_structure_elicitation:
  required:
    - squad_name: "kebab-case identifier"
    - pack_title: "Human-readable title"
    - version: "1.0.0"
    - author: "Organization or person"
    - entry_agent: "Primary activation agent id (default: {squad_name}-chief)"
    - slash_prefix: "camelCase for slash skills"

  derived:
    - pack_path: "squads/{squad_name}/"
    - outputs_path: ".aiox/squad-runtime/create-squad/{squad_name}/"
    - skill_surface_path: ".claude/skills/{PackTitle}/"

  pattern_library:
    - prefix: "2-letter code (e.g., CP for Copy)"
    - initial_patterns:
      - "{PREFIX}-001: Core Process"
      - "{PREFIX}-002: Quality Standard"
      - "{PREFIX}-003: Exception Handling"
```

### Step 1.1: Load Squad Type Definitions

```yaml
load_squad_types:
  file: "data/squad-type-definitions.yaml"
  required: true

  extract:
    - available_types: "List of squad archetypes"
    - type_characteristics: "What each type is optimized for"
    - recommended_agent_counts: "Min/max agents per type"
    - template_approaches: "Operational vs Expert patterns"
```

### Step 1.2: Select Squad Type

```yaml
squad_type_selection:
  decision_inputs:
    - domain: "{domain}"
    - purpose: "{purpose}"
    - use_cases: "{use_cases}"
    - target_user: "{target_user}"

  matching_criteria:
    - domain_alignment: "Which type best fits the domain?"
    - use_case_coverage: "Which type covers the most use cases?"
    - complexity_match: "Does type complexity match squad needs?"

  elicit_if_ambiguous:
    question: "Multiple squad types could work. Which approach fits best?"
    present_options:
      - type: "Describe each matching type with pros/cons"
      - recommendation: "Highlight best match with rationale"
```

**Decision Point:**
```
IF clear single match:
    -> AUTO-SELECT and inform user
ELSE IF 2-3 close matches:
    -> PRESENT options with rationale
    -> ASK user to select
ELSE:
    -> WARN: "Domain is unusual. Using generic template."
    -> PROCEED with generic structure
```

### Step 1.3: Choose Template Approach

```yaml
template_approach:
  operational:
    description: "Agents defined by function/role, not based on specific experts"
    best_for: "Technical domains, process-heavy workflows"
    agent_naming: "Function-based (e.g., analyzer, writer, reviewer)"
    example: "data-squad with etl-agent, query-optimizer, schema-designer"

  expert_template:
    description: "Agents modeled after domain expert archetypes using web research"
    best_for: "Creative domains, knowledge-heavy workflows"
    agent_naming: "Archetype-based (e.g., strategist, master-copywriter)"
    example: "copy-squad with headline-specialist, persuasion-expert"

  decision_tree:
    - IF domain is technical/process-oriented:
        approach: "operational"
    - ELSE IF domain is creative/knowledge-oriented:
        approach: "expert_template"
    - ELSE:
        approach: "hybrid (operational core + expert specialists)"
```

### Step 1.4: Map Use Cases to Agent Roles

```yaml
use_case_agent_mapping:
  for_each_use_case:
    - use_case: "{use_case}"
      derive:
        - required_roles: "What agent roles are needed?"
        - tier_suggestion: "Which tier should handle this?"
        - shared_roles: "Can an existing role cover this?"

  output:
    agent_roster:
      - role: "diagnostician"
        tier: 0
        covers_use_cases: ["all - initial analysis"]
      - role: "primary-executor"
        tier: 1
        covers_use_cases: ["use_case_1", "use_case_2"]
      - role: "specialist"
        tier: 3
        covers_use_cases: ["use_case_3"]

  constraints:
    min_agents: 3
    max_agents: 12
    must_have_tier_0: true
    must_have_orchestrator: true
```

## Output

```yaml
discover_output:
  # Discovery outputs
  viability_score: "{score}/10"
  decision: "create_new | extend | abort_duplicate"
  squad_name: "{squad_name}"
  pack_title: "{Pack Title}"
  entry_agent: "{squad_name}-chief"
  slash_prefix: "{prefix}"
  pattern_prefix: "{PREFIX}"
  mode: "incremental | yolo"
  workspace_context:
    domain_match: "exact | partial | none"
    related_products: ["list"]
  # Type selection outputs
  squad_type: "{selected_type}"
  template_approach: "operational | expert_template | hybrid"
  agent_roster:
    - role: "{role_name}"
      tier: "{0|1|2|3}"
      covers: ["use_case_list"]
  total_agents_planned: "{N}"
  checkpoint_status: "PASS | FAIL"
```

## Acceptance Criteria

- [ ] Domain viability score >= 6/10 (or user override for 4-5 range)
- [ ] No duplicate squad exists (or user confirmed extend/override)
- [ ] Squad name defined in kebab-case
- [ ] Entry agent ID defined
- [ ] Workspace domain awareness completed
- [ ] Native scope gate evaluated
- [ ] Squad type selected from `squad-type-definitions.yaml`
- [ ] Template approach defined (operational, expert_template, or hybrid)
- [ ] Agent roster has at least one Tier 0 agent
- [ ] Agent roster has an orchestrator role
- [ ] All input use cases mapped to at least one agent role
- [ ] Agent count within 3-12 range

## Veto Conditions

- **VETO-SQD-001:** Squad directory already exists AND user has not explicitly confirmed overwrite
- Domain viability score < 4 with no override
- `workflows_mapped >= 10 OR agents_needed >= 8` without valid PRD
- Agent roster missing Tier 0 agent
- Agent roster missing orchestrator
- Use cases left unmapped to any agent role
- Agent count exceeds 12 without PRD/epic execution mode

## Related Documents

- `create-squad.md` (parent composed task)
- `create-squad-design.md` (next step)
- `data/squad-type-definitions.yaml`
- `data/tier-system-framework.md`
- `checklists/squad-checklist.md`

---

_Task Version: 2.0.0 (merged from: create-squad-discover v1.0.0 + create-squad-select-type v1.0.0)_
_Last Updated: 2026-03-27_
