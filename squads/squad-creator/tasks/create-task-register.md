# Task: Register Task in Squad

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-register` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-task-register
name: Register Task in Squad
category: task-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Register the newly created task in the squad's config.yaml,
  update agent dependencies, refresh the README task list,
  and document integration notes.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_register
Output: artifact::create_task_register
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Complete the task creation lifecycle by registering the new task in the squad ecosystem -- updating config.yaml, agent dependencies, and README. Without registration, the task exists as a file but is not discoverable or executable through squad commands.

## Prerequisites

- [ ] Task file validated and saved (from create-task-validate)
- [ ] SC_TSK_001 quality gate PASSED
- [ ] Squad config.yaml exists and is writable

## Inputs

```yaml
inputs:
  - name: validated_task
    type: object
    required: true
    source: previous_task
    description: "Output from create-task-validate"

  - name: squad_name
    type: string
    required: true
    source: previous_task
    description: "Target squad identifier"

  - name: task_id
    type: string
    required: true
    source: previous_task
    description: "Task identifier"

  - name: executor_agent
    type: string
    required: true
    source: previous_task
    description: "Agent that executes this task"
```

## Workflow / Steps

### Step 1: Update Squad config.yaml

Add the new task to the squad's configuration:

```yaml
update_config:
  file: "squads/{squad_name}/config.yaml"
  action: "Add task entry"
  fields:
    - task_id
    - task_name
    - executor_agent
    - execution_type
```

### Step 2: Update Agent Dependencies

If the task is assigned to a specific agent, update that agent's dependencies:

```yaml
update_agent:
  file: "squads/{squad_name}/agents/{agent_name}.md"
  section: "dependencies.tasks"
  action: "Add task_id to task list"
```

### Step 3: Update Squad README

Add the new task to the squad's README task listing:

```yaml
update_readme:
  file: "squads/{squad_name}/README.md"
  section: "Tasks"
  action: "Add task entry with description"
  format: "| {task_id} | {purpose} | {executor} |"
```

### Step 4: Document Integration Notes

Record which agents use this task, prerequisite tasks, and follow-up tasks:

```yaml
integration_notes:
  agents_that_use:
    - "{executor_agent}"
    - "squad-chief (orchestration)"
  prerequisite_tasks: ["tasks that must run before"]
  follow_up_tasks: ["tasks that can run after"]
  handoff_to:
    - agent: "squad-chief"
      when: "Create more tasks"
    - agent: "{executor_agent}"
      when: "Execute the task"
```

### Step 5: Verify Registration

```yaml
verify:
  checks:
    - config_updated: "Task appears in config.yaml"
    - agent_updated: "Task listed in agent dependencies"
    - readme_updated: "Task listed in README"
    - command_executable: "Task can be invoked via *{command}"
```

## Output

```yaml
output:
  name: registration_complete
  format: yaml
  structure:
    task_id: "{task_id}"
    squad: "{squad_name}"
    config_updated: true
    agent_updated: true
    readme_updated: true
    command: "*{task-command}"
    execution_agent: "@{squad}:{agent}"
```

## Acceptance Criteria

- [ ] Task registered in squad config.yaml
- [ ] Agent dependencies updated (if applicable)
- [ ] README task list updated
- [ ] Integration notes documented
- [ ] Task is executable via command

## Veto Conditions

- Task file does not exist at expected path
- SC_TSK_001 did not pass (task not validated)
- config.yaml is malformed after update

## Related Documents

- `create-task-validate.md` -- Prerequisite (provides validated task)
- `create-task.md` -- Parent composed task
- Squad `config.yaml` -- Registration target
- Squad `README.md` -- Documentation target

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 5 (Handoff)_
