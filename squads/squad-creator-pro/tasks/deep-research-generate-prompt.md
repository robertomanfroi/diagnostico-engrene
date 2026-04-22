<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deep-research-generate-prompt
  task_name: Generate Deep Research Prompt
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
  - '.1: Component 1 -- REFINED TOPIC'
  - '.2: Component 2 -- CONTEXT'
  - '.3: Component 3 -- SCOPE (4-6 items)'
  - '.4: Component 4 -- REQUIREMENTS (3-4 items)'
  - '.5: Component 5 -- RECOMMENDED SOURCES (3-4 types)'
  acceptance_criteria:
  - Research prompt covers all 7 components [threshold: >= 7]
  - REFINED TOPIC is specific, not generic [threshold: >= 1 specific topic]
  - SCOPE has 4-6 investigative angles with sub-points [threshold: >= 4]
  - REQUIREMENTS specify source priority and analysis depth [threshold: >= 3]
  - RECOMMENDED SOURCES list concrete titles/types (not vague) [threshold: >= 3]
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


# Task: Generate Deep Research Prompt

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `deep-research-generate-prompt` |
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
| **Phase** | 2 of 4 |
| **Created** | 2026-03-26 |
| **Part of** | squads/squad-creator-pro |

## Purpose

Generate a comprehensive research prompt using the 7-component meta-framework. This prompt drives Phase 3 (Execute Research) and ensures research is strategic, scoped, and actionable rather than generic.

## Prerequisites

- Phase 1 output (local_catalog, research_mode, research_note) if specialist exists
- All required inputs provided and non-empty

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `agent_purpose` | string | Yes | What the agent should do |
| `domain` | string | Yes | Area of expertise |
| `specialist_slug` | string | No | If based on human expert |
| `specialist_name` | string | No | Human-readable name |
| `activity` | string | Yes | Specific activity (e.g., "sales-page") |
| `research_mode` | string | No | From Phase 1: `"complementary"` or `"comprehensive"` |
| `research_note` | string | No | From Phase 1: context about local knowledge |

## Workflow / Steps

### Step 2.1: Component 1 -- REFINED TOPIC

Transform the agent purpose into a strategic research title.

```yaml
instruction: |
  Transform the agent purpose into a strategic research title.
  - Expand scope beyond the obvious
  - Include time period if specialist-based
  - Make it specific yet comprehensive

template: |
  "The {Methodology} of {Specialist}: {Expanded Description} ({Time Period})"

example: |
  "The Sales Page Engineering of Gary Halbert: Complete Anatomy of Direct Mail
  Letters that Generated Millions — From Envelope to PS (1970-2007)"
```

### Step 2.2: Component 2 -- CONTEXT

```yaml
instruction: |
  Brief paragraph establishing:
  - What we're building (agent purpose)
  - Why this research matters
  - What we already have (if any)
  - Practical objectives

template: |
  Building an AI agent to {agent_purpose} following {specialist_name}'s REAL
  methodology. {local_knowledge_note}. Need to extract operational frameworks,
  not just theory.
```

### Step 2.3: Component 3 -- SCOPE (4-6 items)

```yaml
instruction: |
  Develop specific angles to investigate:
  - Process/methodology angles
  - Structure/anatomy of outputs
  - Quality criteria from expert
  - Real examples/case studies
  - Modern adaptation considerations
  - Common mistakes/anti-patterns

format: |
  1. {ANGLE_NAME}
     - Sub-point with specific questions
     - Sub-point with specific questions
     - Sub-point with specific questions

  2. {ANGLE_NAME}
     ...
```

### Step 2.4: Component 4 -- REQUIREMENTS (3-4 items)

```yaml
instruction: |
  Parameters for the research:
  - Source priority (primary vs secondary)
  - Analysis depth needed
  - Format preferences
  - What to include/exclude

examples:
  - "Prioritize expert's own words (quotes, rules, principles)"
  - "Include line-by-line analysis of real examples"
  - "Differentiate personal style vs universal principles"
  - "Extract operational templates, not just concepts"
```

### Step 2.5: Component 5 -- RECOMMENDED SOURCES (3-4 types)

```yaml
instruction: |
  Specific source types to prioritize:
  - Books by the expert
  - Interviews/podcasts
  - Archive materials
  - Case studies/analyses

format: |
  - "{Book/Source Title}" (specific chapters if known)
  - {Expert} interviews/podcasts
  - Archive of {expert}'s work
  - Analysis by students/practitioners
```

### Step 2.6: Component 6 -- EXPECTED RESULTS (3-5 deliverables)

```yaml
instruction: |
  Concrete, actionable outputs:
  - Templates with clear structure
  - Checklists derived from expert criteria
  - Process workflows step-by-step
  - Example databases with analysis

format: |
  1. "{Deliverable Name}" - {What it contains}
  2. "{Deliverable Name}" - {What it contains}
  ...
```

### Step 2.7: Component 7 -- CLARIFYING QUESTIONS (2-3)

```yaml
instruction: |
  Questions to refine the research focus.
  Note: In YOLO mode, these are auto-answered or skipped.

examples:
  - "Should focus be on {A} or {B}?"
  - "Priority: depth on one topic or breadth across many?"
  - "Include modern adaptations or stay pure to original?"
```

## Output

| Artifact | Format | Description |
|----------|--------|-------------|
| Research prompt | Structured text with all 7 components | Ready to drive Phase 3 execution |

The prompt must contain all 7 sections: REFINED TOPIC, CONTEXT, SCOPE, REQUIREMENTS, RECOMMENDED SOURCES, EXPECTED RESULTS, CLARIFYING QUESTIONS.

## Acceptance Criteria

- [ ] Research prompt covers all 7 components [threshold: >= 7]
- [ ] REFINED TOPIC is specific, not generic [threshold: >= 1 specific topic]
- [ ] SCOPE has 4-6 investigative angles with sub-points [threshold: >= 4]
- [ ] REQUIREMENTS specify source priority and analysis depth [threshold: >= 3]
- [ ] RECOMMENDED SOURCES list concrete titles/types (not vague) [threshold: >= 3]
- [ ] EXPECTED RESULTS are actionable deliverables (templates, checklists), not theory [threshold: >= 3]
- [ ] If research_mode is "complementary", prompt focuses on gaps from Phase 1 [threshold: >= 1 gap-focused section]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-DRGP-001 | `agent_purpose`, `domain`, and `activity` must be non-empty | Validate all required inputs | VETO - BLOCK. Request missing inputs before generating prompt. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `deep-research-pre-agent.md` | Parent stub (orchestrator) |
| `deep-research-check-local-knowledge.md` | Previous phase (Phase 1) |
| `deep-research-execute.md` | Next phase (Phase 3) -- consumes this prompt |
| `deep-research-validate.md` | Phase 4 |
| `docs/research/david-ogilvy-research-engineering-meta-framework.md` | Gold standard reference |
