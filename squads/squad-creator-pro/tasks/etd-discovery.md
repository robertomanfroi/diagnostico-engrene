---
task-id: etd-discovery
name: "ETD Phase 1: Discovery (Recognition + Frameworks)"
version: 2.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Descoberta combinada de padroes perceptuais e frameworks requer interpretacao profunda"
estimated-time: 25 min
complexity: medium
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
    - sources: "Fontes validadas com metodologia documentada"

outputs:
  primary:
    - recognition_patterns_yaml: "Bloco YAML com instant_detection, blind_spots, attention_triggers"
    - frameworks_yaml: "Bloco YAML com primary_framework, secondary_frameworks, diagnostic_framework"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-discovery
  task_name: 'ETD Phase 1: Discovery (Recognition + Frameworks)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 25m
  domain: Operational
  input:
  - "{'mind_name': 'Nome do expert a clonar'}"
  - "{'domain': 'Area de expertise'}"
  - "{'sources': 'Fontes validadas com metodologia documentada'}"
  output:
  - "{'recognition_patterns_yaml': 'instant_detection, blind_spots, attention_triggers'}"
  - "{'frameworks_yaml': 'primary_framework, secondary_frameworks, diagnostic_framework'}"
  action_items:
  - Varrer fontes para padroes perceptuais (o que o expert nota que outros nao notam)
  - Extrair frameworks operacionais (o sistema operacional mental)
  acceptance_criteria:
  - 2+ instant_detection patterns com evidence
  - 1+ blind_spot com consequence
  - 2+ attention_triggers com response
  - Framework principal com 3+ steps e evidence
  - 2+ frameworks secundarios com trigger
  - Framework de diagnostico com 3+ questions
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
  pre_condition: "inputs, dependencias e artefatos previos resolvidos antes de iniciar a execucao."
  post_condition: "Recognition patterns e frameworks extraidos. Prontos para fase de extracao de heuristicas."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# ETD Phase 1: Discovery (Recognition + Frameworks)

> **Objetivo:** Varrer as fontes para extrair (A) o que o expert NOTA que outros nao notam e
> (B) os frameworks operacionais que compoe seu "sistema operacional" mental.
>
> **Principio:** Uma unica passagem pelas fontes extraindo ambas as dimensoes simultaneamente.
>
> **Tempo estimado:** 25 minutos

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-DIS-001 | Sources must be available and validated | Verify sources input exists with methodology content | VETO - BLOCK. Run collect-sources first. |
| VETO-DIS-002 | Sources must contain methodology content | Verify at least 3 sources describe processes or methodologies | VETO - BLOCK. Insufficient methodology content. |

---

## Step 1: Recognition Patterns (Radares Mentais)

O que este expert NOTA PRIMEIRO que outros nao notam?

### 1.1 Instant Detection
```yaml
recognition_patterns:
  instant_detection:
    - domain: ""
      pattern: "O que veem em < 2 segundos"
      accuracy: "X/10"
      evidence: ""
```

**Perguntas-guia:**
- "O que este expert ve que ninguem mais ve?"
- "Qual o primeiro sinal que procura em qualquer situacao?"
- "O que faz ele dizer 'isso esta errado' instantaneamente?"

### 1.2 Blind Spots
```yaml
  blind_spots:
    - domain: ""
      what_they_miss: ""
      why: ""
      consequence: ""
```

**Perguntas-guia:**
- "Onde este expert ja errou publicamente?"
- "O que outros experts criticam nele?"

### 1.3 Attention Triggers
```yaml
  attention_triggers:
    - trigger: "Quando ve/ouve..."
      response: "Imediatamente faz..."
      intensity: "alto|medio|baixo"
```

---

## Step 2: Framework Principal (O "Sistema Operacional")

Todo expert tem UM framework que usa para TUDO. Encontre-o.

```yaml
primary_framework:
  name: ""
  creator: "{mind_name}"
  acronym: ""
  purpose: ""
  steps:
    - step: 1
      name: ""
      action: ""
      output: ""
  when_to_use: ""
  when_NOT_to_use: ""
  evidence:
    - source: ""
      quote: ""
```

**Perguntas-guia:**
- "Qual processo ele SEMPRE segue?"
- "O que ele ensina primeiro para iniciantes?"
- "Se pudesse ensinar apenas UMA coisa, o que seria?"

---

## Step 3: Frameworks Secundarios (2-4)

```yaml
secondary_frameworks:
  - name: ""
    purpose: ""
    steps: []
    trigger: "quando usar"
```

---

## Step 4: Framework de Diagnostico

Como o expert AVALIA uma situacao antes de agir?

```yaml
diagnostic_framework:
  name: ""
  questions:
    - "Primeira pergunta que faz"
    - "Segunda pergunta"
    - "Terceira pergunta"
  red_flags: ["sinais de problema"]
  green_flags: ["sinais positivos"]
```

---

## Output

Entregue 2 blocos YAML completos:
1. `recognition_patterns` com instant_detection, blind_spots, attention_triggers
2. `frameworks` com primary_framework, secondary_frameworks, diagnostic_framework

---

## Quality Check

- [ ] 2+ instant_detection patterns com evidence
- [ ] 1+ blind_spot com consequence
- [ ] 2+ attention_triggers com response
- [ ] Framework principal com 3+ steps e evidence
- [ ] 2+ frameworks secundarios com trigger
- [ ] Framework de diagnostico com 3+ questions

**Score minimo:** 5/6 items checked

## Acceptance Criteria

- [ ] Recognition patterns e frameworks extraidos numa unica passagem
- [ ] Todos os outputs rastreavies a fontes
- [ ] Framework principal validado com o usuario (elicit)
