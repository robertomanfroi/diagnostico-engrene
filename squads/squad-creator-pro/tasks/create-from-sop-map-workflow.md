<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-from-sop-map-workflow
  task_name: Create From SOP -- Map + Workflow
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Process Mapping
  - Workflow Synthesis
  - Gap Surface
  acceptance_criteria:
  - Every executable_process mapped to task candidate with executor + guardrails
  - Workflow phases defined with checkpoints and handoffs
  - Open questions surfaced with [MISSING]/[AMBIGUOUS]/[CONFLICT] tags
  - No invented features or processes
  - Processes mapped
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Create From SOP -- Map + Workflow

**Task ID:** create-from-sop-map-workflow
**Parent Task:** `create-from-sop.md`
**Purpose:** Extract processes from classified sources, synthesize workflows, surface gaps
**Execution Type:** Agent
**Model:** `Opus`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Create From SOP -- Map + Workflow |
| **status** | `active` |
| **responsible_executor** | @pedro-valerio |
| **execution_type** | Agent |
| **input** | `source_classification` YAML from load-classify step |
| **output** | Task inventory + workflow map + open questions |
| **action_items** | 3 steps |
| **acceptance_criteria** | Processes mapped, workflows synthesized, gaps surfaced |

---

## Workflow

### Step 2: Process Mapping

For each `executable_process`, extract:

```yaml
mapped_process:
  source_path: string
  task_name: string
  executor: Human | Agent | Hybrid | Worker
  inputs: []
  outputs: []
  checkpoints: []
  guardrails: []
  dependencies: []
```

**Rules:**

- Do not transform context into operational step without evidence in the YAML
- Do not merge different processes just because they live in the same namespace
- Do not lose ownership; each output needs an owner or guardian

### Step 3: Workflow Synthesis

1. Group processes by phase
2. Draw unidirectional flow
3. Declare mandatory checkpoints
4. Convert metadata/status signals into guardrails or quality gates

### Step 4: Gap Surface

Generate `open_questions` whenever:

- A process depends on information that does not exist in any selected YAML
- There is ambiguity of owner/responsible
- The YAML describes state but not action
- There is conflict between selected sources

**Mandatory notation:** mark as `[MISSING]`, `[AMBIGUOUS]`, or `[CONFLICT]`.

---

## Output Contract

```yaml
process_mapping:
  task_inventory:
    - task_name: "{name}"
      source_path: "{path}"
      executor: "Human|Agent|Hybrid|Worker"
      inputs: []
      outputs: []
      checkpoints: []
      guardrails: []
      dependencies: []

  workflow_map:
    phases:
      - phase_id: "{id}"
        name: "{name}"
        tasks: []
        checkpoint: "{criteria}"
        handoff: "{to whom}"

  open_questions:
    - type: "MISSING|AMBIGUOUS|CONFLICT"
      description: "{what is unclear}"
      source: "{which YAML}"
      impact: "{what it blocks}"
```

---

## Completion Criteria

- [ ] Every executable_process mapped to task candidate with executor + guardrails
- [ ] Workflow phases defined with checkpoints and handoffs
- [ ] Open questions surfaced with [MISSING]/[AMBIGUOUS]/[CONFLICT] tags
- [ ] No invented features or processes

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `create-from-sop-brief.md` |
| **Trigger** | Mapping complete |
| **Artifact** | `process_mapping` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of create-from-sop.md_

## Acceptance Criteria

- [ ] Processes mapped
- [ ] workflows synthesized
- [ ] gaps surfaced
