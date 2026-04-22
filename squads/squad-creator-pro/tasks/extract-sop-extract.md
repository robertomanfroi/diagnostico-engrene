---
task-id: extract-sop-extract
name: "3-Pass Extraction (Structure, Anatomy, Decisions)"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Deep semantic extraction from unstructured transcripts. Not deterministic."
haiku_eligible: false
estimated-time: 30 min
complexity: medium

inputs:
  required:
    - transcript_object: "Standardized transcript from Phase 1"
    - preparation_notes: "Language, speakers, chunks from Phase 1"

outputs:
  primary:
    - raw_steps: "All identified process steps"
    - task_anatomy_map: "Each step mapped to Task Anatomy format"
    - decision_rules: "IF/THEN rules extracted from conditions"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-sop-extract
  task_name: 3-Pass Extraction (Structure, Anatomy, Decisions)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - '{''transcript_object'': ''Standardized transcript from Phase 1''}'
  - '{''preparation_notes'': ''Language, speakers, chunks from Phase 1''}'
  output:
  - '{''raw_steps'': ''All identified process steps''}'
  - '{''task_anatomy_map'': ''Each step mapped to Task Anatomy format''}'
  - '{''decision_rules'': ''IF/THEN rules extracted from conditions''}'
  action_items:
  - First Pass -- Structure Identification
  - Second Pass -- Task Anatomy Mapping
  - Third Pass -- Decision Rules Extraction
  acceptance_criteria:
  - All process steps identified (even informal)
  - Each step has Task Anatomy (8 fields)
  - Executor type assigned per classification guide
  - Decision rules extracted as IF/THEN
  - Red flags documented
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: 3-Pass Extraction

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-sop-extract` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-sop` (orchestrator stub)
- **Sequence:** Phase 2 of 4
- **Previous Task:** `extract-sop-prepare`
- **Next Task:** `extract-sop-analyze`

## Purpose

Execute 3 extraction passes: identify structure, map to Task Anatomy, and extract decision rules.

## Workflow / Steps

### Step 1: First Pass -- Structure Identification

1. Identify process name and objective
2. List all mentioned steps (even informal)
3. Note all people/roles mentioned
4. Capture all tools/systems referenced
5. Mark decision points ("if", "when", "depends")

**Output:** Raw extraction notes

### Step 2: Second Pass -- Task Anatomy Mapping

For each identified step, extract:

```yaml
step_template:
  task_name: "[Verb] + [Object]"
  responsible_executor: "[Role or @agent]"
  execution_type: "Human | Agent | Hybrid | Worker"
  estimated_time: "[Xh/Xm]"
  input: ["list of inputs"]
  output: ["list of outputs"]
  action_items: ["atomic steps"]
  acceptance_criteria: ["how to verify success"]
```

**Classification Guide:**

| Cognitive Signal | Executor Type |
|------------------|---------------|
| "I look at...", "I check..." | Agent (perception) |
| "I decide based on...", "It depends..." | Hybrid (judgment) |
| "I talk to...", "I convince..." | Human (relationship) |
| "I copy...", "I move...", "I send..." | Worker (deterministic) |

### Step 3: Third Pass -- Decision Rules Extraction

For each "depends", "usually", "sometimes":

1. Identify the condition
2. Identify possible outcomes
3. Translate to IF/THEN rule
4. Mark if automatable or requires human judgment

**Output:** Decision rules table + heuristics list

**Good transcript signals:**
- "First, I do X, then Y, then Z" -- Clear sequence
- "If the client says no, I do A, otherwise B" -- Decision rule
- "I always check this before proceeding" -- Precondition
- "This takes about 30 minutes" -- Time estimate

**Red flag signals:**
- "It depends" (without criteria) -- Needs clarification
- "Joao knows how to do this" -- Single point of failure
- "We figure it out" -- Undocumented exception
- "It's always been this way" -- May be obsolete

## Output

```yaml
raw_steps: [{ step_name, actors, tools, decisions }]
task_anatomy_map: [{ 8-field Task Anatomy per step }]
decision_rules: [{ IF condition THEN action }]
heuristics: [{ pattern-based rules }]
```

## Acceptance Criteria

- [ ] All process steps identified (even informal)
- [ ] Each step has Task Anatomy (8 fields)
- [ ] Executor type assigned per classification guide
- [ ] Decision rules extracted as IF/THEN
- [ ] Red flags documented

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-sop.md` | Parent orchestrator |
| `extract-sop-prepare.md` | Previous phase |
| `extract-sop-analyze.md` | Next phase |
