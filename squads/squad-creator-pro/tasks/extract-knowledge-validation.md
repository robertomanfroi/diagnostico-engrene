---
task: "Extract Knowledge: Final Validation & Handoff"
task_id: extract-knowledge-validation
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Validation is checklist-driven with human review -- deterministic."
haiku_eligible: true
responsavel: "@tim-ferriss"
responsavel_type: agent
atomic_layer: task
elicit: true
phase: discovery
parent_task: extract-knowledge

workflows:
  - wf-extraction-pipeline
config:
  - squad-config
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-knowledge-validation
  task_name: Final Validation & Handoff
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - '.1: Aggregate Gate Results'
  - '.2: Final Validation Checklist'
  - '.3: Cross-Phase Anti-Invention Audit'
  - '.4: Prepare Handoff'
  acceptance_criteria:
  - 'Phase 0: SOURCE_COVERAGE gate passed'
  - 'Phase 1: FRAMEWORK_QUALITY gate passed (if applicable)'
  - 'Phase 2: SOP_QUALITY gate passed (if applicable)'
  - 'Phase 3: CHECKLIST_QUALITY gate passed (if applicable)'
  - 'Anti-invention checks: ALL passed'
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Final Validation & Handoff

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-knowledge-validation` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid (Agent validates, Human confirms)` |
| **Estimated Time** | `15-20 min` |

## Metadata

| Key | Value |
|-----|-------|
| Parent Task | `extract-knowledge` |
| Phase | 4 (Final Validation) |
| Gate | All gates aggregated |
| Depends On | Phases 0-3 (whichever were executed based on format) |

## Purpose

Aggregate all quality gate results, run final anti-invention validation across all outputs, and prepare handoff to downstream tasks (create-squad or validate-squad).

## Prerequisites

- All applicable phases completed (based on `format` parameter)
- All phase-level quality gates passed
- Output files written to correct locations

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| format | enum | Yes | Which phases ran: `triplet`, `framework`, `sop`, `checklist` |
| framework_file | file | Conditional | Framework output (if format includes framework) |
| sop_file | file | Conditional | SOP output (if format includes sop) |
| checklist_file | file | Conditional | Checklist output (if format includes checklist) |

## Workflow / Steps

### Step 4.1: Aggregate Gate Results

```yaml
quality_gate_summary:
  - gate: SOURCE_COVERAGE
    phase: 0
    blocking: true
    status: "[ ]"
  - gate: FRAMEWORK_QUALITY
    phase: 1
    blocking: true
    status: "[ ]"
  - gate: SOP_QUALITY
    phase: 2
    blocking: true
    status: "[ ]"
  - gate: CHECKLIST_QUALITY
    phase: 3
    blocking: true
    status: "[ ]"
```

Mark gates as N/A for skipped phases based on `format`.

### Step 4.2: Final Validation Checklist

- [ ] Phase 0: SOURCE_COVERAGE gate passed
- [ ] Phase 1: FRAMEWORK_QUALITY gate passed (if applicable)
- [ ] Phase 2: SOP_QUALITY gate passed (if applicable)
- [ ] Phase 3: CHECKLIST_QUALITY gate passed (if applicable)
- [ ] Anti-invention checks: ALL passed
- [ ] Appendix D: 50+ citations present (if SOP was generated)
- [ ] Triplet files: All created in correct locations

### Step 4.3: Cross-Phase Anti-Invention Audit

Scan all output files for red flag signals:

**Red flag signals (BLOCK if found):**
- "Generally, experts recommend..." -- NO SOURCE
- "Best practice is to..." -- GENERIC
- "It's common to add..." -- INVENTED
- Step without [SOURCE: ...] -- UNTRACEABLE

**Good signals (expected):**
- `> "The formula is X = Y / Z" [SOURCE: p.47]` -- Literal quote
- `Step derived from: "First, do X, then Y" [SOURCE: min 23:45]` -- Traceable
- `Example from author: Gym Launch case [SOURCE: Ch.5]` -- Author's example

### Step 4.4: Prepare Handoff

```yaml
handoff:
  to: "create-squad OR validate-squad"
  trigger: "all_gates_passed = true"
  data_transferred:
    - framework.md
    - sop.md
    - blueprint.yaml
    - checklist.md
  validation: "Human confirms zero invention"
```

**Elicit for human confirmation:**
```
Extracao completa. Resumo:

- Formato: {format}
- Gates passados: {X}/{Y}
- Citacoes totais: {count}
- Arquivos gerados: {file_list}

Confirma que o output esta livre de invencao? (sim/nao)
```

## Output

| Output | Type | Description |
|--------|------|-------------|
| validation_report | Summary | Gate results + anti-invention audit + handoff readiness |

## Acceptance Criteria

- [ ] All applicable quality gates aggregated and passed [threshold: score >= 0.8]
- [ ] Cross-phase anti-invention audit completed with zero red flags [threshold: >= 0]
- [ ] All output files verified at correct locations [threshold: >= 1]
- [ ] Human confirmation of zero invention obtained [threshold: >= 1]
- [ ] Handoff artifact prepared for downstream task [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EKN-002 | Existing files must be backed up before overwrite | Check if output files already exist | VETO - BLOCK. Create backup before writing. |

## Error Handling

| Error | Cause | Resolution |
|-------|-------|------------|
| SOURCE_COVERAGE failed | Insufficient material | Request more sources, run Deep Research |
| FRAMEWORK_QUALITY failed | Missing citations | Return to sources, find literal quotes |
| SOP_QUALITY failed | <50 references | Expand Appendix D, cite more |
| CHECKLIST_QUALITY failed | Invented checkboxes | Remove non-SOP items |
| Invention detected | Unsourced claim | Delete or find source |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-knowledge.md` | Parent task (stub) |
| `extract-knowledge-source-validation.md` | Phase 0 |
| `extract-knowledge-framework.md` | Phase 1 |
| `extract-knowledge-sop.md` | Phase 2 |
| `extract-knowledge-checklist.md` | Phase 3 |
| `create-squad.md` | Downstream consumer |
| `validate-squad.md` | Downstream consumer |
