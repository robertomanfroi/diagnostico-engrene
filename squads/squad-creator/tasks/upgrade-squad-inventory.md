# Task: Inventory Squad Components

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad-inventory` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: upgrade-squad-inventory
name: "Inventory Squad Components"
category: upgrade
agent: squad-chief
elicit: false
autonomous: true
description: "Scan squad directory, categorize components, extract metadata, build component registry"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::upgrade_squad_inventory
Output: artifact::upgrade_squad_inventory
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Scan an existing squad's file structure and build a complete component inventory with structural metadata. This is the foundational data-collection step for any upgrade workflow -- no analysis, no judgment, just facts.

## Prerequisites

- Squad directory exists at `squads/{squad_name}/`
- `config.yaml` exists (at minimum) in the squad root

## Inputs

| Parameter | Type | Required | Description | Example |
|-----------|------|----------|-------------|---------|
| `squad_name` | string | Yes | Name of squad to inventory | `"copy"`, `"legal"` |
| `focus` | enum | No | Limit scan to component type | `agents`, `tasks`, `workflows`, `all` |

## Workflow

### Step 1: Scan Squad Structure

1. List all files in `squads/{squad_name}/`
2. Categorize by type: `agents/`, `tasks/`, `workflows/`, `templates/`, `checklists/`, `data/`
3. Count lines per file
4. Extract version from `config.yaml`

### Step 2: Extract Component Metadata

For each component, extract key structural metadata:

**Agent files -- check presence of:**
- `ACTIVATION-NOTICE`
- `IDE-FILE-RESOLUTION`
- `activation-instructions:`
- `agent:` section
- `persona:` section
- `core_principles:` section
- `commands:` section
- `dependencies:` section

**Task files -- check presence of:**
- `task_name` / Task ID
- `status`
- `responsible_executor`
- `execution_type`
- `input` / Inputs
- `output` / Outputs / Output
- `action_items` / Workflow / Steps
- `acceptance_criteria`

**Workflow files -- check presence of:**
- `phases:` section
- `checkpoints:` section
- `outputs:` section

### Step 3: Build Component Registry

Assemble into structured inventory:

```yaml
inventory:
  squad: "{squad_name}"
  version: "{from config.yaml}"
  scan_date: "{ISO date}"
  totals:
    agents: N
    tasks: N
    workflows: N
    templates: N
    checklists: N
    data: N
  component_details:
    agents:
      count: N
      files:
        - name: "agent-name.md"
          lines: N
          has_activation_notice: true/false
          has_yaml_block: true/false
    tasks:
      count: N
      files:
        - name: "task-name.md"
          lines: N
          has_8_fields: true/false
    workflows:
      count: N
      files: [...]
    templates:
      count: N
      files: [...]
    checklists:
      count: N
      files: [...]
    data:
      count: N
      files: [...]
```

## Output

| Output | Format | Location |
|--------|--------|----------|
| Component Inventory | YAML | Passed to next task (`upgrade-squad-gap`) |
| Console Summary | Table | Displayed to user |

**Console summary format:**

```
INVENTORY: {squad_name} v{version}

| Category    | Count | Total Lines |
|-------------|-------|-------------|
| Agents      | 25    | 12,400      |
| Tasks       | 45    | 8,200       |
| Workflows   | 3     | 1,100       |
| Templates   | 12    | 3,500       |
| Checklists  | 8     | 2,100       |
| Data        | 5     | 1,800       |
```

## Acceptance Criteria

- [ ] All files in squad directory are cataloged and categorized
- [ ] Line counts are accurate per file
- [ ] Structural metadata extracted for agents, tasks, and workflows
- [ ] Output conforms to the inventory YAML schema above
- [ ] Focus parameter correctly limits scan scope when provided

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-INV-001"
    condition: "Squad directory does not exist"
    trigger: "Before Step 1"
    block_behavior: "HALT with clear error message"
```

## Related Documents

| Reference | File |
|-----------|------|
| Parent orchestrator | `tasks/upgrade-squad.md` |
| Next task | `tasks/upgrade-squad-gap.md` |
| Agent Quality Gate | `checklists/agent-quality-gate.md` |
| Task Anatomy | `checklists/task-anatomy-checklist.md` |
