<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: pv-audit-overview
  task_name: Process Audit -- Structural Overview
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
  - List Structure
  - Read Config Only
  acceptance_criteria:
  - Agent count and line counts collected
  - Workflow count collected
  - config.yaml read for structure
  - Overview YAML generated
  - Token usage stayed within ~2k budget
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


# Task: Process Audit -- Structural Overview

**Task ID:** pv-audit-overview
**Parent Task:** `pv-audit.md`
**Purpose:** Map squad structure WITHOUT reading full content (~2k token budget)
**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Process Audit -- Structural Overview |
| **status** | `active` |
| **responsible_executor** | @pedro-valerio |
| **execution_type** | Agent |
| **input** | Squad name |
| **output** | `squad_overview` YAML |
| **action_items** | 2 steps |
| **acceptance_criteria** | Structure mapped without reading full file content |

---

## CRITICAL: Token Budget

**This phase: ~2k tokens maximum.**

**NUNCA:**

- Read full agent files
- Read DNA files
- Read more than 1 file (config.yaml only)

---

## Workflow

### Step 1: List Structure

```bash
# Commands to execute:
ls -la squads/{squad}/agents/     # List agents (do not read)
ls -la squads/{squad}/workflows/  # List workflows (do not read)
wc -l squads/{squad}/agents/*.md  # Count lines per agent
```

### Step 2: Read Config Only

**Read ONLY:** `config.yaml` (squad structure)

Generate overview:

```yaml
squad_overview:
  name: "{squad}"
  agent_count: N
  workflow_count: N
  total_lines: N
  largest_agents: [top 3 by lines]
  has_dna_files: true|false
  has_checklists: true|false
```

---

## Output Contract

```yaml
squad_overview:
  name: "{squad}"
  agent_count: {n}
  workflow_count: {n}
  total_lines: {n}
  largest_agents:
    - name: "{agent}"
      lines: {n}
  has_dna_files: true|false
  has_checklists: true|false
  estimated_token_cost: "~{n}k"
```

**HALT:** Show overview and ask user for direction.

---

## Completion Criteria

- [ ] Agent count and line counts collected
- [ ] Workflow count collected
- [ ] config.yaml read for structure
- [ ] Overview YAML generated
- [ ] Token usage stayed within ~2k budget

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `pv-audit-sample.md` |
| **Trigger** | User confirms to proceed |
| **Artifact** | `squad_overview` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of pv-audit.md_

## Acceptance Criteria

- [ ] Structure mapped without reading full file content
