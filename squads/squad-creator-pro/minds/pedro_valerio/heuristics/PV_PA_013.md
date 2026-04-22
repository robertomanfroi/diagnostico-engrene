---
id: "PV_PA_013"
title: "Task-First Primacy"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Atomic Design"
  - "Task Architecture"
pipeline_instances:
  - "task-structuring"
sys_tension:
  tension_with: "Executor-Centric Planning"
  resolution: "Separate task abstraction (logical requirements) from executor binding (implementation). Define what must be done before deciding who/what does it. This preserves flexibility and enables executor substitution without process redefinition."
---

# PV_PA_013 - Task-First Primacy

**Type:** Decision Heuristic
**Phase:** 2 (Atom Formatting)
**Agent:** @hybridOps:process-architect

## Purpose

Never define a process by 'what the Agent does' or 'what the tool does'. Define the exact Task requirements (inputs, outputs, conditions), treating the Executor (Human, Agent, Worker, Clone) as an interchangeable, transversal attribute.

## Configuration

```yaml
PV_PA_013:
  name: "Task-First Primacy"
  phase: 2

  veto_conditions:
    - condition: "task_definition_starts_with_tool_or_executor_identity == true"
      action: "VETO - Define the task logically, then attach the executor."
```

## Application

**Process:** Audit SOPs and task definitions. Strip tool references from the step abstraction. Define outputs clearly, then assign the executor based purely on capability match.

## Decision Tree

```
IF (Process explicitly binds an operation permanently to an identity - e.g. "Ask ChatGPT")
THEN REFACTOR - (Rename to "Generate Draft"; Assign Executor: Agent).
```

## Failure Modes

### Architectural Rigidity
- **Trigger:** Hardcoding 'Agent' into the core step definition.
- **Detection:** When the AI model shifts or a Worker script replaces it, the company has to rebuild the entire operational manual.

---

## Validation

**Paradox Identified:** Task-First philosophy conflicts with Executor-Centric optimization (where immediate executor clarity streamlines allocation). Resolution: decouple task definition (logical layer) from executor binding (physical/runtime layer). A task remains valid regardless of executor type; the abstraction enables future flexibility without redefinition overhead.

**Validation Checklist:**
- [ ] Task definition stands independently without executor reference
- [ ] Outputs are specified before executor assignment
- [ ] Capability matrix used to match executors to tasks
- [ ] Process survives executor substitution without restructuring
- [ ] Documentation reflects task semantics, not executor identity
