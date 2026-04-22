<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deep-research-check-local-knowledge
  task_name: Check Local Knowledge for Deep Research
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
  - '.1: Search MMOS Resources'
  - '.2: Catalog Found Resources'
  - '.3: Determine Research Mode'
  acceptance_criteria:
  - All 4 MMOS search paths are checked [threshold: >= 4]
  - Each found file has path, type, and line count recorded [threshold: >= 1 per file]
  - Relevance to `agent_purpose` is assessed per file [threshold: >= 1 assessment per file]
  - Topics covered and gaps are explicitly listed [threshold: >= 1 topic OR >= 1 gap]
  - Research mode is correctly determined based on 1000-line threshold [threshold: >= 1 mode selected]
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


# Task: Check Local Knowledge for Deep Research

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `deep-research-check-local-knowledge` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `agent` |

## Metadata

| Key | Value |
|-----|-------|
| **Model** | Opus |
| **Haiku Eligible** | NO |
| **Parent Task** | `deep-research-pre-agent` (stub) |
| **Phase** | 1 of 4 |
| **Created** | 2026-03-26 |
| **Part of** | squads/squad-creator-pro |

## Purpose

Search and catalog existing local knowledge (MMOS resources, prior research) for a specialist before executing external research. Determines whether subsequent research should be "comprehensive" (full) or "complementary" (gap-filling only).

## Prerequisites

- `specialist_slug` must be provided (otherwise this phase is skipped entirely)
- MMOS directory structure exists at `.aiox/squad-runtime/minds/`

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `specialist_slug` | string | Yes | Specialist identifier for MMOS lookup |
| `agent_purpose` | string | Yes | What the agent should do (used for relevance assessment) |

## Workflow / Steps

### Step 1.1: Search MMOS Resources

Search the following paths for existing specialist knowledge:

```yaml
search_paths:
  - .aiox/squad-runtime/minds/{specialist_slug}/sources/
  - .aiox/squad-runtime/minds/{specialist_slug}/analysis/
  - .aiox/squad-runtime/minds/{specialist_slug}/synthesis/
  - docs/research/{specialist_slug}-*.md
```

### Step 1.2: Catalog Found Resources

For each file found:

```yaml
for each file found:
  - Record: path, type, line count
  - Assess: relevance to agent_purpose
  - Extract: key topics already covered
```

Produce a structured catalog:

```yaml
output:
  local_catalog:
    files_found: []
    total_lines: N
    topics_covered: []
    gaps_identified: []
```

### Step 1.3: Determine Research Mode

Based on total local knowledge volume, select the research mode:

```python
if total_lines > 1000:
    research_mode = "complementary"  # Focus on gaps
    research_note = f"Already have {total_lines} lines. Focus on: {gaps}"
else:
    research_mode = "comprehensive"  # Full research needed
    research_note = "Limited local knowledge. Comprehensive research needed."
```

## Output

| Artifact | Format | Description |
|----------|--------|-------------|
| `local_catalog` | YAML structure | Files found, line counts, topics covered, gaps identified |
| `research_mode` | string | Either `"complementary"` or `"comprehensive"` |
| `research_note` | string | Human-readable summary for downstream phases |

## Acceptance Criteria

- [ ] All 4 MMOS search paths are checked [threshold: >= 4]
- [ ] Each found file has path, type, and line count recorded [threshold: >= 1 per file]
- [ ] Relevance to `agent_purpose` is assessed per file [threshold: >= 1 assessment per file]
- [ ] Topics covered and gaps are explicitly listed [threshold: >= 1 topic OR >= 1 gap]
- [ ] Research mode is correctly determined based on 1000-line threshold [threshold: >= 1 mode selected]
- [ ] Output catalog is structured YAML, not free text [threshold: >= 1 valid YAML catalog]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-DRCK-001 | `specialist_slug` must be non-empty | Validate input is a non-empty string | VETO - BLOCK. This phase requires a specialist. If no specialist, skip entirely. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `deep-research-pre-agent.md` | Parent stub (orchestrator) |
| `deep-research-generate-prompt.md` | Next phase (Phase 2) |
| `deep-research-execute.md` | Phase 3 |
| `deep-research-validate.md` | Phase 4 |
| `checklists/deep-research-quality.md` | Quality checklist |
