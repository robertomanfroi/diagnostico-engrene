---
task-id: extract-implicit
name: "Extrator de Conhecimento Tacito"
version: 3.0.0
execution_type: Orchestrator
model: Sonnet
model_rationale: "Orchestrator stub -- delegates to atomic sub-tasks. Sonnet for routing decisions."
haiku_eligible: false
note: "Decomposed from v2.0.0 monolith (518 lines) into 5 atomic tasks."
estimated-time: 60-90 min
complexity: high

specialist: "@oalanicolas"
specialist_guidance: |
  Use DNA Mental source curation methodology for source validation.
  Feynman Technique for extraction quality validation.
  SECI Model Externalization (Nonaka & Takeuchi) for tacit-to-explicit conversion.

inputs:
  required:
    - source_corpus: "Conteudo a analisar (livro, aula, conversa, codigo, processo)"
    - source_type: "Tipo de conteudo (livro | aula | conversa | codigo | processo | entrevista)"
    - scope_boundaries: "Limites do escopo de extracao"
  optional:
    - prior_extractions: "Extracoes anteriores para triangulacao"
    - source_metadata: "Metadata da fonte (nome, data, analista)"

outputs:
  primary:
    - implicit_knowledge_report: "Relatorio completo de conhecimento implicito"
    - clone_guardrails: "Guardrails de confianca gerados a partir das evasoes"
    - validation_result: "PASS | NEEDS_REVISION"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit
  task_name: Extrator de Conhecimento Tacito
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 60-90m
  domain: Operational
  input:
  - '{''source_corpus'': ''Conteudo a analisar (livro, aula, conversa, codigo, processo)''}'
  - '{''source_type'': ''Tipo de conteudo (livro | aula | conversa | codigo | processo
    | entrevista)''}'
  - '{''scope_boundaries'': ''Limites do escopo de extracao''}'
  - '{''prior_extractions'': ''Extracoes anteriores para triangulacao''}'
  - '{''source_metadata'': ''Metadata da fonte (nome, data, analista)''}'
  output:
  - '{''implicit_knowledge_report'': ''Relatorio completo de conhecimento implicito''}'
  - '{''clone_guardrails'': ''Guardrails de confianca gerados a partir das evasoes''}'
  - '{''validation_result'': ''PASS | NEEDS_REVISION''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - All veto conditions checked and none triggered
  - 'Output artifact produced: Relatorio completo de conhecimento implicito'
  - Task output validated against quality standards
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
  executor: Clone
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Extrator de Conhecimento Tacito

> **Revelar o que foi decidido sem ser verbalizado**
>
> *"O conhecimento mais perigoso e o que voce nao sabe que nao sabe."*
> *"We can know more than we can tell." -- Michael Polanyi*

---

## Pipeline (5 Atomic Tasks)

| Phase | Task ID | Name | Model | Est. Time |
|-------|---------|------|-------|-----------|
| 1 | `extract-implicit-scan` | Initial Scan | Opus | 10 min |
| 2 | `extract-implicit-analyze` | Deep Analysis (5 Axes) | Opus | 20 min |
| 3 | `extract-implicit-prioritize` | Prioritize Findings | Sonnet | 5 min |
| 4 | `extract-implicit-synthesize` | Synthesize Report + Guardrails | Opus | 15 min |
| 5 | `extract-implicit-validate` | Feynman Validation | Opus | 10 min |

---

## Execution Flow

```
extract-implicit-scan
  | scan_markers
  v
extract-implicit-analyze
  | analysis_findings
  v
extract-implicit-prioritize
  | prioritized_findings
  v
extract-implicit-synthesize
  | implicit_knowledge_report + clone_guardrails
  v
extract-implicit-validate
  | validated_report + validation_result
  v
[DONE if PASS | LOOP to Phase 2 if NEEDS_REVISION]
```

---

## The 5 Axes of Analysis

| Axis | Question | What It Reveals |
|------|----------|-----------------|
| **Premissas** | "Que suposicoes nunca foram questionadas?" | Fundacoes invisiveis |
| **Heuristicas** | "Que regras de decisao nao foram formalizadas?" | Como decisoes sao tomadas na pratica |
| **Pontos Cegos** | "Que riscos ninguem mencionou?" | O que pode matar o projeto |
| **Decisoes Implicitas** | "Que caminhos foram escolhidos por omissao?" | Portas fechadas sem perceber |
| **Evasao Deliberada** | "O que o expert desviou ou minimizou?" | Limites de competencia |

---

## Veto Conditions (Consolidated)

| ID | Condition | Phase | Result |
|----|-----------|-------|--------|
| VETO-EIM-001 | Source corpus must be explicitly defined | Phase 1 | BLOCK |
| VETO-EIM-002 | Existing artifact must be backed up before overwrite | Phase 1 | BLOCK |
| VETO-EIM-003 | CRITICO/ALTO findings must have `[SOURCE:]` evidence | Phase 2 | BLOCK |

---

## Sources

- Nonaka, I. & Takeuchi, H. (1995). *The Knowledge-Creating Company*
- Polanyi, M. (1966). *The Tacit Dimension*
- Adler, M. & Van Doren, C. (1972). *How to Read a Book*
- Parrish, S. (2019). *The Great Mental Models*

---

**Squad Architect | Implicit Knowledge Extractor v3.0**

## Task Anatomy

- **Executor:** Agent
- **Inputs:** source_corpus; source_type; scope_boundaries
- **Outputs:** Relatorio completo de conhecimento implicito; Guardrails de confianca gerados a partir das evasoes; PASS | NEEDS_REVISION
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Relatorio completo de conhecimento implicito
- [ ] Task output validated against quality standards
