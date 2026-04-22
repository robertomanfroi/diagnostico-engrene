---
task: Extract Knowledge (Framework -> SOP -> Checklist)
task_id: extract-knowledge
version: 2.0.0
execution_type: Agent
model: Opus
model_rationale: "Orchestrator stub -- routes to atomic sub-tasks. Opus needed for format-aware routing logic."
haiku_eligible: false
responsavel: "@tim-ferriss"
responsavel_type: agent
atomic_layer: task
elicit: true
phase: discovery
decomposed: true

# Dependencies
workflows:
  - wf-extraction-pipeline
templates:
  - pop-extractor-prompt
config:
  - squad-config
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-knowledge
  task_name: Extract Knowledge from Author Sources
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
  - All gates passed
  - 50+ citations
  - zero invention
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


# Extract Knowledge from Author Sources

**Squad:** squad-creator
**Phase:** Discovery
**Agent:** @tim-ferriss
**Workflow:** wf-extraction-pipeline
**Pattern:** Zero Invention - 100% Source-Based Extraction

## Purpose

Extract complete knowledge triplet (Framework + SOP + Checklist) from author/expert source materials. Guarantees ZERO invented content -- every statement must have a literal citation from the source material.

**Core Principle:** "Se nao esta na fonte, nao existe no output."

## Canonical Owner

- `workflows/wf-extraction-pipeline.yaml` é o owner canônico do pipeline atômico de extração.

## Task Anatomy (HO-TP-001)

| Field | Value |
|-------|-------|
| task_name | Extract Knowledge from Author Sources |
| status | active |
| responsible_executor | @tim-ferriss |
| execution_type | Hybrid (Agent extracts, Human validates) |
| estimated_time | 2-4h per triplet |
| input | author_name, topic, sources_path |
| output | framework.md, sop.md, blueprint.yaml, checklist.md |
| acceptance_criteria | All gates passed, 50+ citations, zero invention |

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| author_name | string | Yes | Author/expert name (e.g., "Alex Hormozi") |
| topic | string | Yes | Specific topic to extract (e.g., "Value Equation") |
| sources_path | path | Yes | Path to source materials (books, transcripts, etc.) |
| output_squad | string | No | Target squad (default: inferred from author) |
| format | enum | No | `triplet` (default), `framework`, `sop`, `checklist` |
| depth | enum | No | `quick`, `standard` (default), `deep` |

## Outputs

| Output | Type | Location | Description |
|--------|------|----------|-------------|
| framework | MD | `squads/{squad}/docs/frameworks/{topic}-framework.md` | Conceptual model (formulas, principles) |
| sop | MD | `squads/{squad}/docs/sops/{topic}-sop.md` | Operational process (steps, executors) |
| blueprint | YAML | `squads/{squad}/docs/sops/{topic}-squad-blueprint.yaml` | Agent configuration |
| checklist | MD | `squads/{squad}/checklists/{topic}-sop-checklist.md` | Validation checklist |

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EKN-001 | Source materials must exist and pass SOURCE_COVERAGE gate | Verify sources_path contains files with relevance score >= 5/10 | VETO - BLOCK. Run collect-sources first. |
| VETO-EKN-002 | Existing files must be backed up before overwrite | Check if output files already exist | VETO - BLOCK. Create backup first. |
| VETO-EKN-003 | Zero-invention constraint must be verifiable | Sources must contain extractable quotes | VETO - BLOCK. |

## Decomposed Sub-Tasks

This task was decomposed from a 593-line monolith into 4 atomic tasks.

| Phase | Sub-Task | Task ID | Gate | Skip If |
|-------|----------|---------|------|---------|
| 0 | [Source Validation](extract-knowledge-source-validation.md) | `extract-knowledge-source-validation` | SOURCE_COVERAGE | Never |
| 1 | [Framework Extraction](extract-knowledge-framework.md) | `extract-knowledge-framework` | FRAMEWORK_QUALITY | format == sop or checklist |
| 2 | [SOP Extraction](extract-knowledge-sop.md) | `extract-knowledge-sop` | SOP_QUALITY | format == framework or checklist |
| 3 | [Checklist Generation](extract-knowledge-checklist.md) | `extract-knowledge-checklist` | CHECKLIST_QUALITY | format == framework or sop |
| 4 | [Final Validation](extract-knowledge-validation.md) | `extract-knowledge-validation` | All gates | Never |

### Execution Flow by Format

| Format | Phases Executed |
|--------|----------------|
| `triplet` (default) | 0 -> 1 -> 2 -> 3 -> 4 |
| `framework` | 0 -> 1 -> 4 |
| `sop` | 0 -> 2 -> 4 |
| `checklist` | 0 -> 3 -> 4 (requires existing SOP) |

## Commands

```bash
# Full triplet extraction
*extract-knowledge "Alex Hormozi" --topic "Value Equation" --sources ./sources/

# Framework only
*extract-knowledge "Alex Hormozi" --topic "Value Equation" --format framework

# SOP from existing framework
*extract-knowledge "Alex Hormozi" --topic "Value Equation" --format sop --framework ./framework.md

# Checklist from existing SOP
*extract-knowledge "Alex Hormozi" --topic "Value Equation" --format checklist --sop ./sop.md
```

## Handoff

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

## Error Handling

| Error | Cause | Resolution |
|-------|-------|------------|
| SOURCE_COVERAGE failed | Insufficient material | Request more sources, run Deep Research |
| FRAMEWORK_QUALITY failed | Missing citations | Return to sources, find literal quotes |
| SOP_QUALITY failed | <50 references | Expand Appendix D, cite more |
| CHECKLIST_QUALITY failed | Invented checkboxes | Remove non-SOP items |
| Invention detected | Unsourced claim | Delete or find source |

---

**Pattern Compliance:** SC-PE-001 | HO-TP-001 | WF-EXTRACTION-PIPELINE
**Decomposition:** v2.0.0 -- 593 lines -> 5 atomic files (2026-03-26)

## Acceptance Criteria

- [ ] All gates passed
- [ ] 50+ citations
- [ ] zero invention
