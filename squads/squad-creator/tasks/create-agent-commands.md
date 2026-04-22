# Task: Define Agent Commands and Capabilities

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-commands` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-agent-commands
name: Define Agent Commands and Capabilities
category: agent-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Define the agent's command set, capabilities list, dependency
  mapping, and integration points (handoffs, synergies) based
  on the persona specification from create-agent-persona.
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_agent_commands
Output: artifact::create_agent_commands
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Translate the persona specification into operational definitions: commands the agent exposes (with visibility levels), capabilities it advertises, task/template/checklist/data dependencies it requires, handoff scenarios to other agents, and routing rules for the squad orchestrator. This phase bridges persona identity with executable behavior.

## Prerequisites

- [ ] `create-agent-persona` completed (persona spec available)
- [ ] Target squad config.yaml loaded (from research phase)
- [ ] Existing squad agents known (for handoff/synergy mapping)

## Inputs

```yaml
inputs:
  - name: persona_output
    type: object
    required: true
    source: create-agent-persona
    description: "Persona spec: name, id, scope, methodology, voice, quality criteria"

  - name: squad_config
    type: object
    required: true
    source: create-agent-research
    description: "Squad config.yaml with existing agents, capabilities, workflows"

  - name: research_output
    type: object
    required: true
    source: create-agent-research
    description: "Domain research: methodologies, frameworks, tools"
```

## Workflow

### Step 1: Derive Commands from Primary Tasks

```yaml
derive_commands:
  source: "persona_output.scope.does (primary tasks)"
  standard_commands:
    - name: help
      visibility: [full, quick, key]
      description: "Show available commands"
    - name: exit
      visibility: [full, quick, key]
      description: "Exit agent mode"
  derive_rule: >
    Each primary task becomes a command. Use verb-noun
    kebab-case naming. Assign visibility levels:
    - full: all commands
    - quick: most-used commands
    - key: essential commands shown in minimal greeting
  elicit_if_ambiguous:
    question: "Which commands should appear in the quick menu?"
```

### Step 2: Define Capabilities

```yaml
define_capabilities:
  source: "persona_output.scope.does + methodology"
  format: "Short capability strings for config.yaml"
  example:
    - "sales-page-creation"
    - "headline-optimization"
    - "persuasion-framework-application"
```

### Step 3: Map Dependencies

```yaml
map_dependencies:
  tasks: "Identify tasks this agent needs (existing or to-be-created)"
  templates: "Identify templates for agent outputs"
  checklists: "Identify quality checklists"
  data: "Identify data/knowledge files needed"
  tools: "Identify MCP tools or external tools"
  validation:
    - "Check each dependency exists in squad path"
    - "Mark as: implemented | partial | to-be-created"
```

### Step 4: Define Handoff Scenarios

```yaml
define_handoffs:
  source: "persona_output.quality.handoff_triggers"
  min_count: 3
  format:
    - agent: "{target-agent-id}"
      when: "{trigger condition}"
      what: "{what to hand off}"
  standard_handoffs:
    - to: "squad-chief"
      when: "Task outside agent scope"
    - to: "qa"
      when: "Output needs quality review"
```

### Step 5: Define Synergies

```yaml
define_synergies:
  source: "squad_config.agents + research_output"
  identify:
    - "Which existing squad agents complement this agent"
    - "What workflows involve this agent"
    - "What routing rules apply"
```

## Output

```yaml
output:
  commands:
    - name: "{command-name}"
      visibility: [full, quick]
      description: "{description}"
  capabilities: ["cap1", "cap2", "cap3"]
  dependencies:
    tasks: [{name: "task.md", status: "implemented|to-be-created"}]
    templates: [{name: "tmpl.md", status: "implemented|to-be-created"}]
    checklists: [{name: "checklist.md", status: "implemented|to-be-created"}]
    data: [{name: "data.yaml", status: "implemented|to-be-created"}]
    tools: ["tool1", "tool2"]
  handoff_to:
    - agent: "{agent-id}"
      when: "{condition}"
  synergies:
    - agent: "{agent-id}"
      relationship: "{description}"
```

## Acceptance Criteria

- [ ] Commands derived from primary tasks with visibility levels
- [ ] Standard commands (*help, *exit) included
- [ ] Capabilities list defined (>= 3)
- [ ] Dependencies mapped with existence status
- [ ] Handoff scenarios >= 3
- [ ] Synergies with existing squad agents identified

## Veto Conditions

- Zero commands defined beyond *help and *exit
- No handoff scenarios defined
- Dependencies reference files outside squad path (self-contained rule)

## Related Documents

- `create-agent-persona.md` -- Prerequisite (persona spec)
- `create-agent-generate.md` -- Next phase (template filling)
- `create-agent.md` -- Orchestrator task
