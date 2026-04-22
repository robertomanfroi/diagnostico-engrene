---
task-id: etd-handoff-triggers
name: "ETD Phase 6: Handoff Triggers (Quando Delega/Para)"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Mapear limites de competência requer análise profunda de autoconsciência"
estimated-time: 10 min
complexity: low
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
    - sources: "Fontes validadas com metodologia documentada"

outputs:
  primary:
    - handoff_triggers_yaml: "Bloco YAML com handoff_triggers, self_awareness, collaboration_patterns"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-handoff-triggers
  task_name: 'ETD Phase 6: Handoff Triggers (Quando Delega/Para)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''domain'': ''Area de expertise''}'
  - '{''sources'': ''Fontes validadas com metodologia documentada''}'
  output:
  - '{''handoff_triggers_yaml'': ''Bloco YAML com handoff_triggers, self_awareness,
    collaboration_patterns''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 1+ handoff trigger identificado com to_whom
  - Self-awareness completo (4 campos)
  - 2+ collaboration patterns documentados
  - Handoff triggers são consistentes com frameworks e domínio
  - 'Output artifact produced: Bloco YAML com handoff_triggers, self_awareness, collaboration_patterns'
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


# ETD Phase 6: Handoff Triggers (Quando Delega/Para)

> **Objetivo:** Mapear quando o expert reconhece que deve passar para outro ou parar.
>
> **Tempo estimado:** 10 minutos

---

## Step 1: Limites de Competencia

```yaml
handoff_triggers:
  - domain: "Area fora da expertise"
    trigger_when: "Situacao especifica"
    typical_response: "O que diz/faz"
    to_whom: "Para quem indica"
    tone: "humilde|diretivo|colaborativo"

  # Exemplo:
  - domain: "Legal compliance"
    trigger_when: "Questoes regulatorias complexas"
    typical_response: "Voce precisa de um advogado. Eu perguntaria a ele..."
    to_whom: "Advogado especializado"
    tone: "humilde + prestativo"
```

**Perguntas-guia:**
- "Que assuntos ele se recusa a opinar?"
- "Para quem ele redireciona?"
- "Como comunica seus limites?"

**Elicit:** Apresente cada handoff trigger e peça validação.

---

## Step 2: Self-Awareness

```yaml
self_awareness:
  knows_limits: true|false
  defensive_about_gaps: true|false
  shares_partial_knowledge: "Compartilha o que sabe antes de delegar?"
  confidence_in_handoff: "Quão confiante ao dizer 'não sei'?"
```

---

## Step 3: Collaboration Patterns

```yaml
collaboration_patterns:
  - with_role: "Designer"
    deference_level: "alto|medio|baixo"
    typical_interaction: ""

  - with_role: "Developer"
    deference_level: ""
    typical_interaction: ""
```

**Perguntas-guia:**
- "Com quais profissionais colabora mais?"
- "Em quais relacionamentos mostra deferência?"
- "Como é o padrão de interação com cada tipo?"

---

## Output

Entregue bloco YAML completo contendo:
- 1+ handoff_triggers com todos os campos preenchidos
- self_awareness com 4 campos preenchidos
- 2+ collaboration_patterns com deference_level

---

## Quality Check

- [ ] 1+ handoff trigger identificado com to_whom
- [ ] Self-awareness completo (4 campos)
- [ ] 2+ collaboration patterns documentados
- [ ] Handoff triggers são consistentes com frameworks e domínio

**Score mínimo:** 3/4 items checked

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain; sources
- **Outputs:** Bloco YAML com handoff_triggers, self_awareness, collaboration_patterns
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Bloco YAML com handoff_triggers, self_awareness, collaboration_patterns
- [ ] Task output validated against quality standards
