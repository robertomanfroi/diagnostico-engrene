<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deconstruct
  task_name: deconstruct (Stub)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Completed deconstruct output artifact'
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
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: deconstruct (Stub)

> **Perguntas de Desconstrucao** | Revelar frameworks ocultos de experts

**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

## Objetivo

Aplicar perguntas de desconstrucao para extrair frameworks, heuristicas e padroes de decisao que o expert usa mas nao articula explicitamente.

## Origem

Metodologia absorvida de Tim Ferriss (4-Hour series, Tools of Titans, Tribe of Mentors).

---

## CHECKPOINT INTEGRAL

```yaml
checkpoint_profundidade_perguntas:
  consult: "OBSESSIONS.clareza_compreensao_profunda"
  question: "Perguntas revelam COMO o expert DECIDE ou so O QUE faz?"
  if_decisao: "Documentar frameworks de decisao"
  if_acao: "Reformular perguntas para focar em decisao (nao acao)"
  rationale: "O QUE faz = superficie. COMO decide = framework real."
```

---

## Sub-Tasks (Atomic Execution)

| # | Sub-Task | File | Responsibility |
|---|----------|------|----------------|
| 1 | Extract | `deconstruct-extract.md` | Apply 7 core questions + complementary questions to extract raw answers |
| 2 | Synthesize | `deconstruct-synthesize.md` | Synthesize frameworks, heuristics, anti-patterns, and citations from answers |

---

## Execution Flow

```
Step 1: deconstruct-extract
  Input: expert source material (interview, book, podcast, or direct access)
  Output: raw answers to 7 core questions + complementary answers

Step 2: deconstruct-synthesize
  Input: raw answers from extraction
  Output: frameworks, heuristics, anti-patterns, citations report
```

---

## Completion Criteria

| Criterio | Status |
|----------|--------|
| 7 perguntas respondidas (ou marcadas como nao encontradas) | [ ] |
| Cada resposta com [SOURCE:] | [ ] |
| Pelo menos 3 frameworks identificados | [ ] |
| Pelo menos 5 heuristicas extraidas | [ ] |
| Anti-patterns documentados | [ ] |

---

_Task Version: 2.0.0_
_Atomized: 2026-03-26_
_Sub-tasks: deconstruct-extract, deconstruct-synthesize_

*"As perguntas certas revelam o que o expert sabe mas nao articula."*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** Task-specific context and prior pipeline outputs
- **Outputs:** Completed deconstruct output artifact
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Completed deconstruct output artifact
- [ ] Task output validated against quality standards
