---
task-id: extract-implicit-synthesize
name: "Synthesize Output Report and Clone Guardrails"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Executive synthesis, guardrail generation, and next-step recommendations require deep contextual reasoning. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 15 min
complexity: high

inputs:
  required:
    - analysis_findings: "Achados classificados por eixo (output de extract-implicit-analyze)"
    - prioritized_findings: "Top 5 + meta-patterns (output de extract-implicit-prioritize)"
  optional:
    - source_metadata: "Metadata da fonte analisada (nome, data, analista)"

outputs:
  primary:
    - implicit_knowledge_report: "Relatorio completo de conhecimento implicito no template padrao"
    - clone_guardrails: "Guardrails de confianca gerados a partir das evasoes"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit-synthesize
  task_name: Synthesize Output Report and Clone Guardrails
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 15m
  domain: Operational
  input:
  - '{''analysis_findings'': ''Achados classificados por eixo (output de extract-implicit-analyze)''}'
  - '{''prioritized_findings'': ''Top 5 + meta-patterns (output de extract-implicit-prioritize)''}'
  - '{''source_metadata'': ''Metadata da fonte analisada (nome, data, analista)''}'
  output:
  - '{''implicit_knowledge_report'': ''Relatorio completo de conhecimento implicito
    no template padrao''}'
  - '{''clone_guardrails'': ''Guardrails de confianca gerados a partir das evasoes''}'
  action_items:
  - Render All 5 Axis Sections
  - Generate Executive Synthesis
  - Generate Clone Guardrails
  - Assemble Complete Report
  acceptance_criteria:
  - All 5 axis sections rendered with correct template format
  - Executive synthesis includes Top 5 table and meta-patterns
  - Next steps are actionable (not generic)
  - Clone Guardrails generated from evasion findings
  - Boundary rules formatted as SE/ENTAO rules
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


# Task: Synthesize Output Report and Clone Guardrails

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-implicit-synthesize` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-implicit` (orchestrator stub)
- **Sequence:** Phase 4 of 5
- **Previous Task:** `extract-implicit-prioritize`
- **Next Task:** `extract-implicit-validate`

## Purpose

Assemble the final output report from all analyzed findings and prioritization data. Generate Clone Guardrails from evasion findings and produce the executive synthesis with actionable next steps.

## Prerequisites

- `extract-implicit-analyze` and `extract-implicit-prioritize` both completed
- All CRITICO/ALTO findings have evidence anchors

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `analysis_findings` | Yes | All findings from 5-axis analysis |
| `prioritized_findings` | Yes | Top 5 + meta-patterns + ranked list |
| `source_metadata` | No | Source name, analysis date, analyst |

## Workflow / Steps

### Step 1: Render All 5 Axis Sections

For each axis, render findings using these per-item fields:

| Axis | Prefix | Required Fields Per Item |
|------|--------|------------------------|
| Premissas | P{N} | Evidencia [SOURCE:], O que esta sendo assumido, Impacto, Pergunta |
| Heuristicas | H{N} | Padrao SE/ENTAO, Evidencia [SOURCE:], Por que importa, Formalizar? |
| Pontos Cegos | PC{N} | O que nao foi discutido, Evidencia da ausencia, Impacto, Cenario de risco, Pergunta |
| Decisoes | D{N} | Escolhido por omissao, Alternativas, Evidencia [SOURCE:], Impacto, Pergunta |
| Evasao | EV{N} | Tema evitado, Sinal de evasao, Evidencia [SOURCE:], Tipo (CONSCIOUS/HABITUAL/SCOPE_LIMIT), Implicacao, Triangulacao |

Each item rendered as `### {Prefix}: {nome}` with bullet fields below.

### Step 2: Generate Executive Synthesis

Using `prioritized_findings.top_5` and `prioritized_findings.meta_patterns`, render:
- **Top 5 table:** `| # | Tipo (P/H/PC/D/EV) | Item | Impacto | Pergunta-Chave |`
- **Meta-patterns** list from prioritization phase
- **3 actionable next steps:** (1) immediate for most critical, (2) unblock others, (3) prevention

### Step 3: Generate Clone Guardrails

From evasion findings, derive confidence guardrails:

| Confidence | When | Clone Rule |
|------------|------|------------|
| ALTA | Expert strong on topic | Respond with frameworks and [SOURCE:] |
| MEDIA | Habitual evasion | "Minha experiencia aqui e limitada, mas..." |
| BAIXA | Topic actively avoided | "Recomendo consultar [X]." |

Generate SE/ENTAO boundary rules per avoided topic. If user insists on avoided topic, never invent -- admit limitation.

### Step 4: Assemble Complete Report

Combine into final markdown with structure: Metadata header (Fonte, Data, Analista), sections 1-5 (per axis), Sintese Executiva, Clone Guardrails.

## Output

Two artifacts:

1. **implicit_knowledge_report:** Complete markdown report following the template above
2. **clone_guardrails:** Extracted guardrails section (also embedded in report)

## Acceptance Criteria

- [ ] All 5 axis sections rendered with correct template format [threshold: >= 5]
- [ ] Executive synthesis includes Top 5 table and meta-patterns [threshold: >= 1]
- [ ] Next steps are actionable (not generic) [threshold: >= 3]
- [ ] Clone Guardrails generated from evasion findings [threshold: >= 1]
- [ ] Boundary rules formatted as SE/ENTAO rules [threshold: >= 1]
- [ ] Report metadata header complete (fonte, data, analista) [threshold: >= 3]

## Veto Conditions

None specific to this phase. Parent veto conditions apply.

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-implicit.md` | Parent orchestrator |
| `extract-implicit-prioritize.md` | Previous phase (prioritization) |
| `extract-implicit-validate.md` | Next phase (Feynman validation) |
