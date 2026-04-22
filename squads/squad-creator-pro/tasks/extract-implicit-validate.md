---
task-id: extract-implicit-validate
name: "Feynman Validation of Implicit Knowledge Extraction"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Feynman validation requires explaining complex findings simply and identifying gaps in own reasoning. Opus for self-critique depth."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - implicit_knowledge_report: "Relatorio completo (output de extract-implicit-synthesize)"
    - analysis_findings: "Achados brutos para re-verificacao"

outputs:
  primary:
    - validated_report: "Relatorio validado com status de cada check"
    - validation_result: "PASS | NEEDS_REVISION com gaps identificados"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit-validate
  task_name: Feynman Validation of Implicit Knowledge Extraction
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''implicit_knowledge_report'': ''Relatorio completo (output de extract-implicit-synthesize)''}'
  - '{''analysis_findings'': ''Achados brutos para re-verificacao''}'
  output:
  - '{''validated_report'': ''Relatorio validado com status de cada check''}'
  - '{''validation_result'': ''PASS | NEEDS_REVISION com gaps identificados''}'
  action_items:
  - Feynman Technique Validation
  - Meta-Heuristic Checks
  - Completion Criteria Verification
  - Determine Validation Result
  - Generate Validation Report
  acceptance_criteria:
  - Feynman validation applied to all CRITICO findings
  - All 3 meta-heuristic checks executed
  - 8-point completion criteria checked with explicit pass/fail
  - Validation verdict determined (PASS or NEEDS_REVISION)
  - If NEEDS_REVISION, specific gaps and revision targets documented
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


# Task: Feynman Validation of Implicit Knowledge Extraction

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-implicit-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-implicit` (orchestrator stub)
- **Sequence:** Phase 5 of 5
- **Previous Task:** `extract-implicit-synthesize`

## Purpose

Validate the quality of the implicit knowledge extraction using Feynman Technique (explain simply or you did not understand), meta-heuristic checks, and completion criteria verification. This is the quality gate before the report is finalized.

## Prerequisites

- `extract-implicit-synthesize` completed with full report and clone guardrails
- Original `analysis_findings` available for cross-check

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `implicit_knowledge_report` | Yes | Complete rendered report |
| `analysis_findings` | Yes | Raw findings for verification |

## Workflow / Steps

### Step 1: Feynman Technique Validation

For each finding category, attempt to explain simply:

| Pergunta | Se NAO conseguir... |
|----------|---------------------|
| Consigo explicar esta premissa em 1 frase? | Premissa nao esta clara |
| Consigo dar 3 exemplos desta heuristica? | Heuristica pode ser falsa |
| Consigo explicar POR QUE este ponto cego importa? | Impacto nao foi entendido |
| Consigo explicar alternativas a decisao implicita? | Decisao nao foi mapeada |

For each finding that fails Feynman validation:
- Flag as `needs_revision: true`
- Document the gap: what could not be explained simply

### Step 2: Meta-Heuristic Checks

Apply the 3 meta-heuristics:

**Meta 1: "Quem ja faz isso bem?"**

```yaml
checkpoint_humble_meta:
  question: "Frameworks existentes foram consultados ANTES de criar categorias proprias?"
  if_pesquisou: "Pesquisou referencias antes de inventar"
  if_inventou: "PARAR e pesquisar frameworks existentes primeiro"
  rationale: "Expert em processo: sabe COMO extrair. Humilde: nao assume que sabe TUDO."
```

**Meta 2: "O que Polanyi/Nonaka/Adler diriam?"**
- Is the Externalization correct per SECI Model?
- Are we at the Analytical/Syntopical level per Adler?

**Meta 3: "Consigo explicar para um iniciante?" (Feynman)**
- Final pass: if any finding remains opaque after simplification attempt, it needs rework.

### Step 3: Completion Criteria Verification

Check each criterion:

| Criterio | Status |
|----------|--------|
| 5 eixos analisados (P, H, PC, D, EV) | [ ] |
| Cada item com [SOURCE:] ou justificativa de ausencia | [ ] |
| Impacto classificado (CRITICO/ALTO/MEDIO) | [ ] |
| Pergunta-chave para cada item | [ ] |
| Top 5 priorizado | [ ] |
| Sintese executiva completa | [ ] |
| Clone Guardrails gerados a partir das evasoes | [ ] |
| Adversarial Stress Test aplicado nas evasoes | [ ] |

### Step 4: Determine Validation Result

```yaml
validation_logic:
  PASS:
    condition: "All 8 completion criteria met AND Feynman checks pass for all CRITICO items"
    action: "Report is final"
  NEEDS_REVISION:
    condition: "Any completion criterion fails OR Feynman check fails for CRITICO item"
    action: "Return to relevant phase with specific gaps documented"
```

### Step 5: Generate Validation Report

```yaml
validation_report:
  result: "PASS | NEEDS_REVISION"
  completion_criteria:
    five_axes_analyzed: true
    source_anchors_present: true
    impact_classified: true
    key_questions_present: true
    top_5_prioritized: true
    executive_synthesis_complete: true
    clone_guardrails_generated: true
    adversarial_stress_test_applied: true
  feynman_checks:
    premissas_clear: true
    heuristicas_exemplified: true
    pontos_cegos_impact_explained: true
    decisoes_alternatives_mapped: true
  meta_heuristics:
    existing_frameworks_consulted: true
    seci_externalization_correct: true
    beginner_explainable: true
  gaps_identified: []
  revision_targets: []
```

## Output

```yaml
validated_report: "{finalized report if PASS, annotated report if NEEDS_REVISION}"
validation_result:
  verdict: "PASS | NEEDS_REVISION"
  score: "0/8"
  gaps: []
  revision_targets: []
```

## Acceptance Criteria

- [ ] Feynman validation applied to all CRITICO findings [threshold: >= 1]
- [ ] All 3 meta-heuristic checks executed [threshold: >= 3]
- [ ] 8-point completion criteria checked with explicit pass/fail [threshold: >= 8]
- [ ] Validation verdict determined (PASS or NEEDS_REVISION) [threshold: >= 1]
- [ ] If NEEDS_REVISION, specific gaps and revision targets documented [threshold: >= 1]
- [ ] If PASS, report marked as finalized [threshold: >= 1]

## Veto Conditions

None specific to this phase. Parent veto conditions apply.

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-implicit.md` | Parent orchestrator |
| `extract-implicit-synthesize.md` | Previous phase (output assembly) |

## Sources

- Nonaka, I. & Takeuchi, H. (1995). *The Knowledge-Creating Company*
- Polanyi, M. (1966). *The Tacit Dimension*
- Adler, M. & Van Doren, C. (1972). *How to Read a Book*
- Parrish, S. (2019). *The Great Mental Models*
