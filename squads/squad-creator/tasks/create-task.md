# Task: Create Squad Task (Composed)

**Task ID:** create-task
**Execution Type:** Hybrid (Composed)
**Domain:** `Tactical`
**Purpose:** Create a single workflow task following Task Anatomy standard (8 fields)
**Orchestrator:** @squad-chief
**Mode:** Elicitation-based (interactive)
**Quality Standard:** AIOX Level (300+ lines simple, 500+ lines complex)
**Model:** `Sonnet`
**Haiku Eligible:** NO

**Type:** Composed Task -- orchestrates 6 atomic sub-tasks in sequence.

**Accountability:** `human: squad-operator | scope: full`

---


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
agent: squad-chief
Input: request::create_task
Output: artifact::create_task
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Execution Sequence

```
INPUT (task_purpose + squad_name)
    |
[1. CLASSIFY]     create-task-classify.md
    |              Task vs Workflow, target squad, executor type
    |
[2. ANATOMY]      create-task-anatomy.md
    |              Define all 8 required Task Anatomy fields
    |
[3. EXECUTOR]     create-task-executor.md
    |              Guardrails, checkpoints, review triggers
    |
[4. GENERATE]     create-task-generate.md
    |              Produce task file from template + anatomy + executor
    |
[5. VALIDATE]     create-task-validate.md
    |              SC_TSK_001 quality gate, fix, save
    |
[6. REGISTER]     create-task-register.md
    |              config.yaml, agent deps, README
    |
OUTPUT: Validated task file + registered in squad
```

## Sub-Task Reference

| # | Task ID | Phase | Responsibility | Executor |
|---|---------|-------|----------------|----------|
| 1 | `create-task-classify` | Classification | Task vs Workflow, squad, executor | Hybrid |
| 2 | `create-task-anatomy` | Anatomy | 8 required fields via elicitation | Hybrid |
| 3 | `create-task-executor` | Executor Design | Guardrails, checkpoints | Agent |
| 4 | `create-task-generate` | Creation | File generation from template | Agent |
| 5 | `create-task-validate` | Validation | SC_TSK_001 quality gate | Agent |
| 6 | `create-task-register` | Registration | Squad config + README update | Worker |

## Frameworks Used

- `data/executor-decision-tree.md` -- Executor assignment (Sub-task 1)
- `data/executor-matrix-framework.md` -- Executor profiles (Sub-task 3)
- `data/decision-heuristics-framework.md` -- Quality gate logic (Sub-task 5)
- `data/quality-dimensions-framework.md` -- Task validation (Sub-task 5)

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `task_purpose` | string | Yes | What the task should accomplish |
| `task_name` | string | Yes | Human-readable name |
| `squad_name` | string | Yes | Target squad |
| `complexity` | enum | No | `"simple"` or `"complex"` |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Task File | `squads/{squad_name}/tasks/{task_id}.md` | Complete task definition |
| Updated Config | `squads/{squad_name}/config.yaml` | Task registered |
| Updated README | `squads/{squad_name}/README.md` | Task listed |

## Heuristics Reference

| Heuristic ID | Name | Sub-Task | Blocking |
|--------------|------|----------|----------|
| SC_ANA_001 | Task Anatomy Complete | create-task-anatomy | Yes |
| SC_TSK_001 | Task Quality Gate | create-task-validate | Yes |

## Error Handling

| Error | Sub-Task | Action |
|-------|----------|--------|
| Should be Workflow | classify | Redirect to `*create-workflow` |
| Missing anatomy field | anatomy | Return to elicitation for that field |
| Validation fails | validate | Fix and re-validate (max 2 iterations) |

---

_Task Version: 3.0 (decomposed)_
_Last Updated: 2026-03-26_
_Sub-tasks: 6 atomic tasks_
**Output Schema:** `squads/squad-creator/config/workflow-yaml-schema.yaml`

