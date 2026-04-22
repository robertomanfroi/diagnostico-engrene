<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deep-research-pre-agent
  task_name: Deep Research Pre-Agent (Orchestrator Stub)
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
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Research prompt covers all 7 components
  - Local knowledge checked first (if specialist)
  - Research document >= 500 lines
  - At least 3 primary source citations
  - At least 4/6 scope sections covered
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


# Task: Deep Research Pre-Agent (Orchestrator Stub)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `deep-research-pre-agent` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `orchestrator` |

## Metadata

| Key | Value |
|-----|-------|
| **Model** | Opus |
| **Haiku Eligible** | NO |
| **Decomposed** | 2026-03-26 |
| **Original Lines** | 583 |
| **Atomic Tasks** | 4 |
| **Created** | 2026-01-22 |
| **Part of** | squads/squad-creator-pro |

## Purpose

Generate a comprehensive deep research prompt and execute research to establish the knowledge foundation BEFORE creating an agent. This ensures agents are built on REAL methodologies from domain experts, not generic LLM knowledge.

**Problem:** Agents created without research are weak and generic. Research FIRST, then create agent based on real frameworks.

**Gold Standard Reference:**
- Research: `docs/research/david-ogilvy-research-engineering-meta-framework.md` (1,179 lines)

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `agent_purpose` | string | Yes | What the agent should do |
| `domain` | string | Yes | Area of expertise |
| `specialist_slug` | string | No | If based on human expert |
| `specialist_name` | string | No | Human-readable name |
| `activity` | string | Yes | Specific activity (e.g., "sales-page") |

## Pipeline (4 Phases)

| Phase | Task File | Condition | Description |
|-------|-----------|-----------|-------------|
| 1 | `deep-research-check-local-knowledge.md` | Only if `specialist_slug` provided | Search MMOS, catalog resources, determine research mode |
| 2 | `deep-research-generate-prompt.md` | Always | Generate 7-component research prompt |
| 3 | `deep-research-execute.md` | Always | Process local + web research, produce document |
| 4 | `deep-research-validate.md` | Always | Score quality, retry if < 60% (max 2 retries) |

### Data Flow

```
Phase 1 ──> local_catalog, research_mode, research_note
                │
Phase 2 ──> research_prompt (7 components)
                │
Phase 3 ──> docs/research/{slug}-{activity}-research.md
                │
Phase 4 ──> validation_result (PASS/CONDITIONAL/FAIL)
                │
                └──> retry Phase 3 if FAIL (max 2)
```

## Output

- `docs/research/{specialist_slug}-{activity}-research.md` (target: 500+ lines)
- Quality score >= 60% (pass threshold)

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-research-then-create-agent.yaml` (Steps 2-5 for research)

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-DRP-001 | `agent_purpose`, `domain`, and `activity` must be non-empty | Validate required inputs | VETO - BLOCK |
| VETO-DRP-002 | Existing research at target path must be backed up | Check file existence | VETO - BLOCK |
| VETO-DRP-003 | Quality score must meet minimum threshold | Validate >= 60% after Phase 4 | VETO - BLOCK (retry max 2) |

## Acceptance Criteria

- [ ] Research prompt covers all 7 components
- [ ] Local knowledge checked first (if specialist)
- [ ] Research document >= 500 lines
- [ ] At least 3 primary source citations
- [ ] At least 4/6 scope sections covered
- [ ] Contains actionable frameworks (not just theory)
- [ ] All claims have source attribution
- [ ] Quality score >= 60%

## Checklist Reference

Before marking this task complete, verify against: `checklists/deep-research-quality.md`

## Error Handling

| Scenario | Action |
|----------|--------|
| No local knowledge found | Continue with web-only research |
| WebSearch returns few results | Try alternative query formulations |
| Research < 500 lines after 2 retries | Accept partial, flag for enrichment |
| Specialist not in MMOS | Treat as comprehensive research |

## Integration

Called by: `workflows/wf-research-then-create-agent.yaml` (Steps 2-5)
Tools used: WebSearch, WebFetch, Read, Write

## Related Documents

| Document | Relationship |
|----------|-------------|
| `deep-research-check-local-knowledge.md` | Phase 1 atomic task |
| `deep-research-generate-prompt.md` | Phase 2 atomic task |
| `deep-research-execute.md` | Phase 3 atomic task |
| `deep-research-validate.md` | Phase 4 atomic task |
| `checklists/deep-research-quality.md` | Quality checklist |

**Created:** 2026-01-22 | **Decomposed:** 2026-03-26
