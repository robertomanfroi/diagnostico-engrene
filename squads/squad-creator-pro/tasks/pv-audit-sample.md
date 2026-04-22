<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: pv-audit-sample
  task_name: Process Audit -- Pattern Sample
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
  - Select Sample
  - Apply Diagnostic Framework
  - Extrapolate
  acceptance_criteria:
  - Process depends on executor goodwill
  - Instructions outside the system
  - Wrong paths possible but "not recommended"
  - No veto conditions
  - Veto conditions block wrong paths
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Process Audit -- Pattern Sample

**Task ID:** pv-audit-sample
**Parent Task:** `pv-audit.md`
**Purpose:** Identify patterns with representative sample using diagnostic framework (~5k token budget)
**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Process Audit -- Pattern Sample |
| **status** | `active` |
| **responsible_executor** | @pedro-valerio |
| **execution_type** | Agent |
| **input** | `squad_overview` YAML from overview phase |
| **output** | `sample_analysis` YAML with patterns and flags |
| **action_items** | 3 steps |
| **acceptance_criteria** | Sample analyzed, patterns found, flags documented |

---

## CRITICAL: Token Budget

**This phase: ~5k tokens maximum.**

**Read ONLY (max 3 files):**

- 1 agent SMALL (< 200 lines)
- 1 agent MEDIUM (200-400 lines)
- 1 main workflow (if exists)

---

## Workflow

### Step 1: Select Sample

From `squad_overview`, pick:

- Smallest agent by line count
- One mid-sized agent
- Primary workflow (if any)

### Step 2: Apply Diagnostic Framework

For each sampled file, ask:

- "If the executor does not read the instructions, what happens?"
- "If the executor tries to skip a step, can they?"
- "If the executor makes a mistake, does the system detect it automatically?"

**Check Red Flags:**

- [ ] Process depends on executor goodwill
- [ ] Instructions outside the system
- [ ] Wrong paths possible but "not recommended"
- [ ] No veto conditions

**Check Green Flags:**

- [ ] Veto conditions block wrong paths
- [ ] Checklist inline in the task itself
- [ ] Handoff rules defined
- [ ] Smoke tests specified

### Step 3: Extrapolate

Based on sample, project patterns across the full squad.

---

## Mode: Full Audit (`--all`)

Process in batches of 3 agents:

```
Batch 1/N: agent-1, agent-2, agent-3
  -> Read 3 agents
  -> Apply diagnostic framework
  -> Partial output
  -> [CONTINUE to next batch]

Batch 2/N: agent-4, agent-5, agent-6
  -> ...
```

**Between batches:** Show progress and ask if user wants to continue.

---

## Output Contract

```yaml
sample_analysis:
  agents_sampled: ["{small}", "{medium}"]
  workflow_sampled: "{name}"
  patterns_found:
    consistent:
      - "{pattern that repeats}"
    inconsistent:
      - "{pattern that varies}"
  red_flags: []
  green_flags: []
  extrapolation: |
    "Based on sample of 2/{total} agents..."
```

**HALT:** Show analysis and ask if user wants deep-dive.

---

## Completion Criteria

- [ ] Sample selected (1 small + 1 medium agent + 1 workflow)
- [ ] Diagnostic framework applied to each
- [ ] Red and green flags documented
- [ ] Extrapolation generated
- [ ] Token budget respected (~5k)

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `pv-audit-deep-dive.md` (on-demand) |
| **Trigger** | User requests specific deep-dive |
| **Artifact** | `sample_analysis` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of pv-audit.md_

## Acceptance Criteria

- [ ] Sample analyzed
- [ ] patterns found
- [ ] flags documented
