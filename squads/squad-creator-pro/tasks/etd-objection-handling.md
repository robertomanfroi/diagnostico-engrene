---
task-id: etd-objection-handling
name: "ETD Phase 5: Objection Handling (Resposta a Desafios)"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Mapear padrões de resposta requer interpretação de tom e estilo comunicativo"
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
    - objection_handling_yaml: "Bloco YAML com common_objections, pushback_triggers, argumentation_style"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-objection-handling
  task_name: 'ETD Phase 5: Objection Handling (Resposta a Desafios)'
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
  - '{''objection_handling_yaml'': ''Bloco YAML com common_objections, pushback_triggers,
    argumentation_style''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 2+ objection responses documentadas com tone
  - 2+ pushback triggers com auto_response
  - Argumentation style completo (4 campos)
  - Tons são consistentes com persona extraída nas fases anteriores
  - 'Output artifact produced: Bloco YAML com common_objections, pushback_triggers,
    argumentation_style'
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


# ETD Phase 5: Objection Handling (Resposta a Desafios)

> **Objetivo:** Mapear como o expert responde quando é questionado ou desafiado.
>
> **Tempo estimado:** 10 minutos

---

## Step 1: Respostas a Objecoes Comuns

```yaml
objection_handling:
  common_objections:
    - objection: "Mas X é mais eficiente"
      typical_response: ""
      tone: "educativo|defensivo|agressivo|dismissivo"
      evidence: ""

  # Exemplo Dan Kennedy:
  common_objections:
    - objection: "Isso é muito caro"
      typical_response: "Preco é o que voce paga, valor é o que voce recebe"
      tone: "educativo + firme"
```

**Perguntas-guia:**
- "Que objeções ele ouve com mais frequência?"
- "Como responde a cada uma?"
- "Muda de tom dependendo da objeção?"

**Elicit:** Apresente cada resposta a objeção e peça validação.

---

## Step 2: Pushback Triggers

O que faz o expert reagir mais fortemente?

```yaml
pushback_triggers:
  - trigger: "Quando questionam sua expertise"
    auto_response: ""
    escalation: "como escala se pressionado mais"

  - trigger: "Quando sugerem atalho antiético"
    auto_response: ""
```

**Perguntas-guia:**
- "O que faz ele ficar visivelmente irritado?"
- "Que tipo de crítica ele não tolera?"
- "Como escala quando pressionado?"

---

## Step 3: Estilo de Argumentacao

```yaml
argumentation_style:
  debate_preference: "socrático|agressivo|colaborativo|evita"
  use_of_evidence: "dados|anedotas|autoridade|analogias"
  admission_willingness: "nunca|raro|quando errado|facilmente"
  recovery_when_wrong: "como se recupera quando está errado"
```

---

## Output

Entregue bloco YAML completo contendo:
- 2+ common_objections com response + tone
- 2+ pushback_triggers com auto_response
- argumentation_style completo (todos os 4 campos)

---

## Quality Check

- [ ] 2+ objection responses documentadas com tone
- [ ] 2+ pushback triggers com auto_response
- [ ] Argumentation style completo (4 campos)
- [ ] Tons são consistentes com persona extraída nas fases anteriores

**Score mínimo:** 3/4 items checked

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain; sources
- **Outputs:** Bloco YAML com common_objections, pushback_triggers, argumentation_style
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Bloco YAML com common_objections, pushback_triggers, argumentation_style
- [ ] Task output validated against quality standards
