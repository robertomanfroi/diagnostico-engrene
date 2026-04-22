<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deep-research-validate
  task_name: Validate Deep Research Output
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
  - '.1: Check Minimum Requirements'
  - '.2: Calculate Quality Score'
  - '.3: Determine Verdict'
  - '.4: Handle Failure (Retry Logic)'
  acceptance_criteria:
  - All 4 minimum requirements checked [threshold: >= 4]
  - Quality score calculated with correct weights (30/25/25/20) [threshold: >= 60%]
  - Verdict correctly determined against thresholds [threshold: >= 1 verdict]
  - 'On FAIL with retries remaining: Phase 3 re-triggered with adjusted queries [threshold: <= 2 retries]'
  - 'On FAIL after max retries: partial research returned with explicit warning [threshold: >= 1 warning]'
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


# Task: Validate Deep Research Output

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `deep-research-validate` |
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
| **Phase** | 4 of 4 |
| **Created** | 2026-03-26 |
| **Part of** | squads/squad-creator-pro |

## Purpose

Validate the research document produced in Phase 3 against minimum quality thresholds. Score the output, determine pass/conditional/fail, and trigger retry if below threshold.

## Prerequisites

- Research document from Phase 3 at `docs/research/{slug}-{activity}-research.md`
- Research prompt from Phase 2 (to verify scope coverage)

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `research_document_path` | string | Yes | Path to the research document from Phase 3 |
| `research_prompt` | structured text | Yes | The 7-component prompt (for scope coverage check) |
| `retry_count` | integer | No | Current retry attempt (0-2), default 0 |

## Workflow / Steps

### Step 4.1: Check Minimum Requirements

Verify the research document meets baseline thresholds:

```yaml
minimum_requirements:
  total_lines: 500
  primary_sources: 3
  scope_coverage: 4/6 sections
  actionable_content: true  # Has processes, not just theory
```

### Step 4.2: Calculate Quality Score

Score the document across 4 weighted dimensions:

```yaml
quality_score:
  primary_evidence: 30%  # Quotes, real examples
  scope_coverage: 25%    # Coverage of prompt scope sections
  actionable_processes: 25%  # Workflows, templates, checklists (not just theory)
  source_credibility: 20%   # Quality and variety of sources cited
```

### Step 4.3: Determine Verdict

```yaml
thresholds:
  pass: ">= 80%"
  conditional: "60-79%"
  fail: "< 60%"
```

| Verdict | Score | Action |
|---------|-------|--------|
| PASS | >= 80% | Accept research document, proceed to agent creation |
| CONDITIONAL | 60-79% | Accept with warning, flag weak areas for manual enrichment |
| FAIL | < 60% | Trigger retry (if retries remaining) or accept partial with warning |

### Step 4.4: Handle Failure (Retry Logic)

```yaml
if quality_score < 60:
  retry_count += 1
  if retry_count <= 2:
    - Adjust queries (broader or more specific based on gaps)
    - Re-execute Phase 3 (deep-research-execute) with retry_count
  else:
    - Return partial research with warning
    - Flag for manual enrichment
    - Log: "Research quality below threshold after 2 retries"
```

## Output

| Artifact | Format | Description |
|----------|--------|-------------|
| `validation_result` | YAML | Verdict (PASS/CONDITIONAL/FAIL), score breakdown, gaps |
| Updated research metadata | Appended to research doc | Quality score added to Research Metadata section |

Example validation result:

```yaml
validation_result:
  verdict: "PASS"
  quality_score: 85
  breakdown:
    primary_evidence: 28/30
    scope_coverage: 20/25
    actionable_processes: 22/25
    source_credibility: 15/20
  minimum_requirements:
    total_lines: 1247  # >= 500 OK
    primary_sources: 5  # >= 3 OK
    scope_coverage: "5/6"  # >= 4/6 OK
    actionable_content: true
  gaps: []
  retry_count: 0
```

## Acceptance Criteria

- [ ] All 4 minimum requirements checked [threshold: >= 4]
- [ ] Quality score calculated with correct weights (30/25/25/20) [threshold: >= 60%]
- [ ] Verdict correctly determined against thresholds [threshold: >= 1 verdict]
- [ ] On FAIL with retries remaining: Phase 3 re-triggered with adjusted queries [threshold: <= 2 retries]
- [ ] On FAIL after max retries: partial research returned with explicit warning [threshold: >= 1 warning]
- [ ] Quality score written to research document's metadata section [threshold: >= 1]
- [ ] Validation result is structured YAML, not free text [threshold: >= 1 valid YAML]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-DRV-001 | Research quality score must meet minimum threshold | Validate quality_score >= 60% | VETO - BLOCK. Retry research with adjusted queries (max 2 retries) or flag for manual enrichment. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `deep-research-pre-agent.md` | Parent stub (orchestrator) |
| `deep-research-check-local-knowledge.md` | Phase 1 |
| `deep-research-generate-prompt.md` | Phase 2 |
| `deep-research-execute.md` | Phase 3 (produces the document validated here) |
| `checklists/deep-research-quality.md` | Quality checklist |
