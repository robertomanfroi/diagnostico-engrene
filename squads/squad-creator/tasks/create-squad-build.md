# Task: Squad Build — Components Creation & Integration

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad-build` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-squad-build
name: "Squad Build & Integration"
category: squad-creation
agent: squad-chief
elicit: false
autonomous: true
description: "Create all squad components (agents, orchestrator, workflows, tasks), wire internal dependencies, create knowledge base, generate documentation, prepare COO handoff, and emit the publish contract."
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical
merged_from:
  - create-squad-components v1.0.0
  - create-squad-integrate v1.0.0

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_squad_build
Output: artifact::create_squad_build
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Create the core functional components of the squad -- agents from templates enriched with domain research, the orchestrator agent with routing logic, multi-step workflows with checkpoints, and atomic tasks following Task Anatomy. Then wire all components together by verifying cross-references, creating the domain knowledge base, generating complete documentation, and emitting the contract that the publish phase will use. Building and integrating are one continuous act of construction.

## Prerequisites

- [ ] `create-squad-design` completed (directory structure exists, architecture defined)
- [ ] Agent roster with tier assignments available (from discover phase)
- [ ] Templates available: `templates/agent-tmpl.md`, `templates/workflow-tmpl.yaml`
- [ ] Frameworks loaded: `data/executor-matrix-framework.md`
- [ ] WebSearch tool available (for domain research)
- [ ] `config.yaml` has valid `entry_agent` and `workspace_integration.level`

## Inputs

```yaml
inputs:
  design_output:
    type: object
    required: true
    description: "Output from create-squad-design"
    fields: [tier_structure, quality_gates, handoffs, architecture_score, base_path, directories_created]
  agent_roster:
    type: list
    required: true
    description: "Agent roles with tier assignments from discover phase"
  squad_name:
    type: string
    required: true
  entry_agent:
    type: string
    required: true
  slash_prefix:
    type: string
    required: true
  template_approach:
    type: string
    required: true
    description: "operational | expert_template | hybrid"
  workspace_integration_level:
    type: string
    required: true
    description: "none | read_only | controlled_runtime_consumer | workspace_first"
```

## Workflow / Steps

### Step 3.2: Create Agents (Template-Driven)

For each agent in the roster:

```yaml
for_each_agent_role:
  template: "templates/agent-tmpl.md"

  process:
    step_1_load_template:
      action: "Load templates/agent-tmpl.md as base structure"

    step_2_research_role:
      action: "Research domain best practices for this role via WebSearch"
      focus:
        - "What methodologies exist for this role?"
        - "What are the key frameworks and processes?"
        - "What vocabulary and terminology is standard?"
        - "What are common anti-patterns?"

    step_3_fill_template:
      action: "Fill template sections with researched content"
      sections:
        - agent_metadata: "name, id, title, icon, whenToUse"
        - persona: "role, style, identity, focus"
        - core_principles: "5-10 principles from domain research"
        - commands: "Role-specific commands"
        - voice_dna: "Domain-appropriate vocabulary and tone (mind clones only)"
        - output_examples: "3+ realistic examples"
        - anti_patterns: "Domain-specific never_do/always_do"
        - completion_criteria: "Per task type"
        - handoff_to: "3+ handoff scenarios"

    step_4_validate:
      action: "Run agent-quality-gate.md for each agent"
      blocking: true
      retry_on_fail: true
      max_retries: 2

  quality_gate:
    blocking: true
    min_lines: 300
    required_sections:
      - output_examples
      - anti_patterns
      - completion_criteria
```

### Step 3.3: Create Orchestrator Agent

```yaml
create_orchestrator:
  agent_id: "{squad_name}-chief"
  role: "Squad Orchestrator"
  tier: "orchestrator"

  special_capabilities:
    - "Route requests to appropriate tier"
    - "Manage multi-agent workflows"
    - "Track context across handoffs"
    - "Report squad status"

  commands:
    - "*help" - List all squad capabilities
    - "*route" - Route request to best agent
    - "*status" - Show current context
    - "*handoff" - Transfer to specific agent

  must_include:
    - tier_routing_logic
    - quality_gate_checks
    - context_preservation
```

### Step 3.4: Create Workflows

```yaml
create_workflows:
  criteria:
    - spans_multiple_agents: true
    - has_intermediate_checkpoints: true
    - output_feeds_next_step: true

  template: "templates/workflow-tmpl.yaml"

  minimum_structure:
    - phases: 3+
    - checkpoints_per_phase: 1+
    - framework_references: 2+

  quality_standard:
    min_lines: 500

  contract_validation:
    blocking: true
    command_per_file: >
      node infrastructure/scripts/squads/validate_workflow_contract_single.cjs
      --file {workflow_file}
      --strict
      --fail-on-warnings
    policy:
      - validate_immediately_after_creation: true
      - stop_on_first_failure: true
      - rerun_after_fix_until_pass: true
```

### Step 3.5: Create Tasks

**Apply: executor-matrix-framework.md**

```yaml
create_tasks:
  task_anatomy:
    - id: "Unique identifier"
    - purpose: "What and why"
    - executor: "Human | Agent | Hybrid | Worker"
    - inputs: "What it needs"
    - preconditions: "What must be true"
    - steps: "How to execute"
    - outputs: "What it produces"
    - validation: "How to verify"

  executor_assignment:
    decision_tree:
      - IF rule_based AND low_stakes -> Worker
      - ELSE IF needs_judgment -> Hybrid (AI draft, human approve)
      - ELSE IF creative_synthesis -> Agent
      - ELSE -> Human

  quality_standard:
    simple_tasks: 300+ lines
    complex_tasks: 500+ lines
```

### Step 4.1: Wire Dependencies

```yaml
wire_dependencies:
  for_each_agent:
    - verify tasks exist
    - verify templates exist
    - verify checklists exist
    - update dependencies block

  missing_dependency_policy:
    - if dependency referenced but doesn't exist -> FAIL phase
    - create explicit remediation queue with missing file paths
    - never create stubs/placeholders in final squad artifacts
```

### Step 4.2: Create Knowledge Base

```yaml
create_knowledge_base:
  file: "data/{squad_name}-kb.md"

  sections:
    - domain_overview: "What this domain is about"
    - key_concepts: "Essential terminology"
    - best_practices: "From domain research"
    - common_patterns: "Reusable patterns"
    - anti_patterns: "What to avoid"
    - regulatory: "If applicable"
```

### Step 4.3: Generate Documentation

```yaml
generate_documentation:
  readme:
    file: "README.md"
    sections:
      - overview
      - installation
      - quick_start
      - agents_list
      - workflows_list
      - tasks_list
      - templates_list
      - usage_examples

  config:
    file: "config.yaml"
    validate: true
```

### Step 4.4: Prepare COO Workspace Handoff

```yaml
prepare_coo_handoff:
  trigger:
    - "created squad declares workspace_integration.level = controlled_runtime_consumer"
    - "created squad declares workspace_integration.level = workspace_first"

  rule: |
    squad-creator nao executa integracao real com workspace.
    Ele prepara um handoff para COO/c-level com contrato, paths e acoes pendentes.

  if_c_level_exists:
    handoff_target: "@coo"
    artifact: ".aiox/squad-runtime/create-squad/{squad_name}/workspace-handoff.yaml"
    must_include:
      - squad_name
      - requested_workspace_level
      - rationale
      - read_paths
      - write_paths
      - template_namespace
      - requested_workspace_actions
      - dependencies_on_existing_domains_or_businesses

  if_c_level_missing:
    artifact: ".aiox/squad-runtime/create-squad/{squad_name}/workspace-handoff.yaml"
    status: "pending_coo_unavailable"
    note: "Nao executar integracao. Apenas registrar handoff pendente."
```

**VETO-SQD-005:** If the workflow attempts to write directly into `workspace/` during squad creation, HALT and generate COO handoff instead.

### Step 4.5: Prepare Activation Surface Contract

```yaml
activation_surface_contract:
  publish_phase: "create-squad-publish"
  must_publish:
    - ".aiox-sync.yaml"
    - ".claude/skills/{slash_prefix}/{entry_agent}/SKILL.md"
    - ".codex/skills/{entry_agent}/SKILL.md"
    - "CLAUDE.md generated registry entry"
  blocking_rule: "Do not finalize squad creation if any activation surface is missing after publish"
```

## Output

```yaml
build_output:
  # Component creation outputs
  agents_created: "{N}"
  all_pass_quality_gate: true
  workflows_created: "{N}"
  tasks_created: "{N}"
  templates_created: "{N}"
  total_lines: "{N}"
  # Integration outputs
  dependencies_wired: true
  missing_dependencies: []
  knowledge_base: "data/{squad_name}-kb.md"
  readme_complete: true
  coo_handoff_status: "not_required | prepared | pending_coo_unavailable"
  activation_surface_contract: "prepared"
  status: "PASS"
```

## Acceptance Criteria

- [ ] All agents pass SC_AGT_001 (300+ lines, output_examples, anti_patterns, completion_criteria; voice_dna for mind clones only)
- [ ] Orchestrator agent exists with routing logic
- [ ] All complex operations have workflows (3+ phases, checkpoints)
- [ ] All workflows pass contract validation (strict mode)
- [ ] All tasks follow Task Anatomy (8 fields)
- [ ] Executor assigned for each task
- [ ] **VETO-SQD-003:** `config.yaml` references a valid entry agent file
- [ ] All internal dependencies verified (no broken references)
- [ ] Knowledge base created with domain content
- [ ] README.md complete with all sections
- [ ] COO handoff prepared when `workspace_integration.level` requires it
- [ ] Activation surface contract prepared for publish phase
- [ ] No stubs or placeholders remain in final artifacts

## Veto Conditions

- **VETO-SQD-003:** Entry agent referenced in `config.yaml` does not exist as a file
- **VETO-SQD-005:** Direct workspace mutation attempted (must use COO handoff)
- Agent fails quality gate after 2 retries
- Workflow fails contract validation after fix cycle
- Missing dependency referenced by an agent with no remediation
- Activation surface contract missing for publish phase

## Related Documents

- `create-squad.md` (parent composed task)
- `create-squad-design.md` (previous step)
- `create-squad-validate.md` (next step)
- `templates/agent-tmpl.md`
- `templates/workflow-tmpl.yaml`
- `data/executor-matrix-framework.md`
- `checklists/agent-quality-gate.md`
- `tasks/sync-ide-skills.md`

---

_Task Version: 1.0.0 (merged from: create-squad-components v1.0.0 + create-squad-integrate v1.0.0)_
_Last Updated: 2026-03-27_
