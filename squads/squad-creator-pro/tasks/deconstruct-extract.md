<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deconstruct-extract
  task_name: Deconstruct -- Extract
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Apply 7 Core Questions
  - Apply Complementary Questions
  - Source Mode Selection
  acceptance_criteria:
  - 7 core questions answered (or marked as not found)
  - Each answer has [SOURCE:] tag
  - Complementary questions applied where answers were vague
  - Source mode correctly selected (interview vs content)
  - 7 questions answered with [SOURCE:] tags
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


# Task: Deconstruct -- Extract

**Task ID:** deconstruct-extract
**Parent Task:** `deconstruct.md`
**Purpose:** Apply 7 core questions + complementary questions to extract raw answers from expert
**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Deconstruct -- Extract |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | Expert source material (interview, book, podcast, or direct access) |
| **output** | Raw answers to 7 core questions + complementary answers |
| **action_items** | 3 steps |
| **acceptance_criteria** | 7 questions answered with [SOURCE:] tags |

---

## Workflow

### Step 1: Apply 7 Core Questions

#### 1. Rotina Matinal

> "What do you do in the first 60 minutes of your day?"

**O que revela:** Prioridades reais, nao declaradas.

#### 2. Piores Recomendacoes

> "What are the worst recommendations in your field?"

**O que revela:** Anti-patterns, o que NAO fazer.

#### 3. Billboard

> "What would you put on a billboard?"

**O que revela:** Mensagem central condensada.

#### 4. Crenca Contraria

> "What is something you believe that others think is insane?"

**O que revela:** Diferencial competitivo, insight unico.

#### 5. Recomeco

> "If you were starting over, what would you do differently?"

**O que revela:** Erros reais, licoes aprendidas.

#### 6. Pareto

> "What's the 20% that produces 80% of results?"

**O que revela:** Alavancas principais, foco essencial.

#### 7. Veto

> "What do you say NO to that most people say YES?"

**O que revela:** Limites, principios nao-negociaveis.

### Step 2: Apply Complementary Questions

**To deepen answers:**

- "Can you give me a specific example?"
- "When did you learn that?"
- "What was the cost of NOT doing that?"
- "How would you teach this to a beginner?"

**To reveal frameworks:**

- "Is there a name for this approach?"
- "Do you have a checklist or process?"
- "What are the steps in order?"
- "What's the first thing you check?"

**To reveal heuristics:**

- "How do you know when to apply this?"
- "What's the trigger that tells you X?"
- "What's your rule of thumb for Y?"
- "When do you break this rule?"

### Step 3: Source Mode Selection

**If direct access to expert (interview):**

1. Ask 7 questions in order
2. Record responses
3. Deepen with complementary questions
4. Document with [SOURCE: minute]

**If using existing content (podcast, book, video):**

1. Search for answers to each question in content
2. Use Grep/search for patterns: "I always", "I never", "biggest mistake"
3. Document with [SOURCE: page/minute]
4. Mark [INFERRED] if no direct answer found

---

## Checkpoints

```yaml
checkpoint_clareza_resposta:
  question: "Resposta traz CLAREZA sobre como o expert decide?"
  if_clareza: "Documentar com [SOURCE:]"
  if_vaga: "Aprofundar com 'Can you give me a specific example?'"

checkpoint_first_principles:
  question: "Desconstrui ate os PRINCIPIOS FUNDAMENTAIS ou aceitei a superficie?"
  if_fundamental: "Framework com principios base documentados"
  if_superficie: "Aplicar 'Por que?' mais 3 vezes ate chegar em axioma"
```

---

## Output Contract

```yaml
extraction:
  expert: "{name}"
  source_type: "interview|podcast|book|video"
  answers:
    - question_id: 1
      question: "Rotina Matinal"
      answer: "{response}"
      source: "[SOURCE: {reference}]"
      framework_revealed: "{if any}"
    - question_id: 2
      question: "Piores Recomendacoes"
      answer: "{response}"
      source: "[SOURCE: {reference}]"
      anti_pattern: "{what to avoid}"
    # ... all 7 questions
  complementary_findings: []
```

---

## Completion Criteria

- [ ] 7 core questions answered (or marked as not found)
- [ ] Each answer has [SOURCE:] tag
- [ ] Complementary questions applied where answers were vague
- [ ] Source mode correctly selected (interview vs content)

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `deconstruct-synthesize.md` |
| **Trigger** | Extraction complete |
| **Artifact** | `extraction` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of deconstruct.md_

## Acceptance Criteria

- [ ] 7 questions answered with [SOURCE:] tags
