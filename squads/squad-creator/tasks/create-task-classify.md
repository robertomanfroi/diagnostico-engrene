# Task: Classify Task Operation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-task-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-task-classify
name: Classify Task Operation
category: task-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Classify whether an operation should be a Task or Workflow,
  identify the target squad, and assign the executor type using
  the executor-decision-tree.md framework.
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_task_classify
Output: artifact::create_task_classify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Determine whether a requested operation is an atomic Task or a multi-phase Workflow, validate the target squad exists, and assign the correct executor type (Worker, Agent, Hybrid, Human) through structured elicitation. This is the foundational classification step that gates all subsequent task creation phases.

## Prerequisites

- [ ] Target squad name is known
- [ ] squad-chief agent is active
- [ ] `data/executor-decision-tree.md` is accessible
- [ ] `data/executor-matrix-framework.md` is accessible

## Inputs

```yaml
inputs:
  - name: task_purpose
    type: string
    required: true
    source: user
    description: "What the task should accomplish"

  - name: task_name
    type: string
    required: true
    source: user
    description: "Human-readable name for the task"

  - name: squad_name
    type: string
    required: true
    source: user
    description: "Target squad identifier"
```

## Workflow / Steps

### Step 1: Task vs Workflow Decision

**Apply: quality_standards.workflow_vs_task_decision**

```yaml
classification_criteria:
  create_WORKFLOW_when:
    - operation_has_3plus_phases: true
    - multiple_agents_involved: true
    - spans_multiple_sessions: true
    - needs_intermediate_checkpoints: true
    - output_from_one_phase_feeds_next: true

  create_TASK_when:
    - atomic_single_session: true
    - single_agent_sufficient: true
    - no_intermediate_checkpoints: true

  decision_tree:
    - IF any workflow criteria met: "Create workflow, not task"
    - ELSE: "Task is appropriate"
```

**Elicitation:**

```yaml
elicit_classification:
  question: "Let's classify this operation. Tell me about it:"
  sub_questions:
    - "Does it have multiple distinct phases (3+)?"
    - "Does it require multiple agents to work together?"
    - "Will it span multiple work sessions?"
    - "Does it need checkpoints between steps?"
  decision:
    if_workflow: "This should be a WORKFLOW. Use *create-workflow instead."
    if_task: "This is correctly a TASK. Let's continue."
```

### Step 2: Identify Target Squad

```yaml
identify_squad:
  validation:
    - check_path: "squads/{squad_name}/"
    - check_exists: true
    - load_config: "config.yaml"
    - identify_agents: "List agents that could execute this task"
  on_not_exists:
    - suggest: "Create squad first with *create-squad"
    - option: "Create task standalone (not recommended)"
```

### Step 3: Assign Executor Type

**Apply: executor-decision-tree.md** (MANDATORY ELICITATION)

Walk through the 6-question elicitation flow:

1. **Q1 - Determinismo:** Same input always produces identical output?
2. **Q2 - Funcao Pura:** Can be implemented as `f(x) -> y` without ambiguity?
3. **Q2a - Implementacao Existente:** Existing library/SDK/API available?
4. **Q2b - ROI de Codificacao:** How frequently will this task execute?
5. **Q3 - Linguagem Natural:** Involves interpreting/generating unstructured text?
6. **Q4 - Impacto de Erro:** What is the impact if the output is wrong?
7. **Q5 - Julgamento Estrategico:** Requires strategic/political/interpersonal judgment?
8. **Q6 - Assistencia AI:** Can AI prepare context to accelerate human decision?

**Decision outcomes:** Worker | Agent | Hybrid | Human

### Step 4: Define Guardrails by Executor Type

```yaml
guardrails_by_type:
  Worker:
    - "Input validation obrigatorio"
    - "Error handling com retry"
    - "Logging de execucao"
    - "Fallback para Hybrid se falhar"
  Agent:
    - "Confidence threshold definido"
    - "Output validation"
    - "Fallback para Hybrid obrigatorio"
    - "Rate limiting"
  Hybrid:
    - "Timeout para review humano"
    - "Escalation path definido"
    - "Feedback loop para melhoria"
    - "Fallback para Human se urgente"
  Human:
    - "Criterios de decisao documentados"
    - "Deadline definido"
    - "Escalation path definido"
    - "Documentacao obrigatoria"
```

## Output

```yaml
output:
  name: phase_0_classification
  format: yaml
  structure:
    classification: "task | workflow"
    squad_name: "{squad-name}"
    pack_path: "squads/{squad-name}/"
    task_id: "{task-name}"
    executor:
      type: "Worker | Agent | Hybrid | Human"
      pattern: "EXEC-{type}-001"
      rationale: "Justification from elicitation path"
      elicitation_path: "Q1 -> Q3 -> Q4 answers"
      guardrails: ["list of guardrails"]
      fallback:
        type: "fallback executor type"
        trigger: "when fallback activates"
```

## Acceptance Criteria

- [ ] Task vs Workflow decision is explicit and justified
- [ ] Target squad exists and config.yaml is loaded
- [ ] Executor type assigned via full elicitation flow (no assumptions)
- [ ] Guardrails defined for the assigned executor type
- [ ] Fallback executor identified
- [ ] Classification output is structured YAML

## Veto Conditions

- Executor assigned without walking the elicitation flow
- Target squad does not exist and user does not acknowledge
- Operation classified as Task when it clearly requires 3+ phases

## Related Documents

- `data/executor-decision-tree.md` -- Primary elicitation framework
- `data/executor-matrix-framework.md` -- Executor profiles reference
- `create-task.md` -- Parent composed task
- `create-workflow.md` -- Alternative if classification yields Workflow

---

_Task Version: 1.0.0_
_Extracted from: create-task.md PHASE 0_
