---
id: "AN_KE_002"
title: "Regra 40/20/40 (The Trinity Allocation)"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Scale"
  - "Framework"
  - "Quality Gate"
pipeline_instances:
  - "resource-allocation"
  - "sprint-ops"
cross_mind_map:
  convergent:
    - id: "PV_PA_002"
      title: "Task-First Assignment (The Invisible Executor)"
      mind: "pedro_valerio"
      resonance: "Ambos defendem critérios cruéis de alocação de capacidade (Code/LLM/Time). AN estabelece um orçamento severo de tempo antes de refatorar; PV estabelece a prioridade da tarefa ignorando o executor como algo secundário. Essência: Alocação impiedosa de recursos baseada em valor."
  tension:
    - id: "PV_PA_016"
      title: "The Hybrid Lean Wastes"
      mind: "pedro_valerio"
      divergence: "O 'slack' (40% não-fazer de AN) entra em tensão conceitual natural com a eliminação de desperdício em Wait Time de PV. Enquanto PV pune o gargalo invisível entre agents, AN protege um buffer maciço intencional de folga estratégica para pensamento."
      invalidates: false
---

# AN_KE_002 - Regra 40/20/40 (The Trinity Allocation)

**Type:** Architecture Heuristic
**Phase:** 2 (Structural Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN002

## Purpose

Travar a distribuição de força e tempo na engenharia de Mind Clones para impedir que a arrogância do "Prompt Engineering" ofusque a mineração crua de dados. O dev tende a achar que qualquer burrice do LLM se resolve somando instruções mágicas. Um prompt não faz milagres se a base cognitiva (Trindade) for lixo. Alan resolve focando a energia pesada (40%) no mapeamento ANTES e no refinamento empírico (40%) DEPOIS, tratando o prompt como mero encanamento (20%).

## Configuration

```yaml
AN_KE_002:
  name: "Regra 40/20/40 (The Trinity Allocation)"
  phase: 2
  zone: "excelencia"
  trigger: "Alocação sistêmica de esforço e budget cognitivo ao iniciar ou iterar um Agente/Clone especialista."

  weights:
    curation_allocation: 1.0
    refinement_allocation: 1.0

  thresholds:
    prompt_engineering_ceiling: 0.2

  veto_conditions:
    - condition: "time_spent_on_prompt_engineering > 0.2_of_total_budget == true"
      action: "VETO - Stop writing rules. You are trying to teach something you haven't extracted. Return to Gold Curation."

  output:
    type: "decision"
    values: ["APPROVE_ALLOCATION", "REVERT_TO_CURATION", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Prompt Magic Delusion (The Hubris)"
    trigger: "Pulando a curadoria pesada da Trindade por pressa de ver a IA 'falar'."
    manifestation: "O dev cospe 3 PDFs lixo genéricos no context window e perde 3 semanas lutando com a IA regurgitando clichês, tentando consertá-la com um prompt gigante."
    detection: "Prompt file System com > 2000 palavras tentando moldar um comportamento tático que devia simplesmente estar em um JSON de RAG documentado."
    recovery: "Zerar o prompt. Trocar fontes Bronze por Ouro na base de indexação."

  - type: "misapplication"
    name: "Over-Engineering the Trivial (The Zealot)"
    trigger: "Um agente simples precisa apenas buscar respostas factuais em uma tabela (DB)."
    manifestation: "Gastar semanas curando e montando 'Trindade Documental' para um mero support-bot factual que não requer estilo, apenas dados diretos."
    detection: "Esforço massivo de 40% inicial aplicado a scripts sem nenhum conhecimento tácito humano."
    recovery: "Limitar a regra 40/20/40 estritamente para Clones Mentais complexos e sistemas de raciocínio. Workers não precisam de Trindade."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Prompt Time Ceiling"
    weight: 1.0
    threshold: "<= 0.20"
    description: "Tempo total gasto lidando com prompts textuais brutos deve ser cravado abaixo de 20% do budget da squad."
  - metric: "Curation Floor"
    weight: 1.0
    threshold: ">= 0.40"
    description: "Pelo menos 40% da sprint foi gasta lapidando, extraindo e validando Ouro (Frameworks, Playbooks) direto da fonte humana?"
  - metric: "Testing Floor"
    weight: 1.0
    threshold: ">= 0.40"
    description: "O restante do tempo é gasto em unit tests táticos provando que a IA realmente age como o Expert nos edge-cases?"
```

## Decision Tree

```javascript
IF (Iniciando a modelagem arquitetural do Agente) {
  EVALUATE("Budget de Tempo da Sessão");
  IF (Time_spent_on_Prompt_Engineering > 0.2) {
    VETO("Excesso na camada de instrução.");
    REVERT_TO_CURATION("Você inseriu muita lógica e poucos dados. Volte aos dados Ouro.");
  } ELSE {
    APPROVE_ALLOCATION("40% Curadoria / 20% Instrução / 40% Validação");
  }
}

NEVER("Tentar consertar gaps ou amnésias cognitivas da IA entupindo o prompt com discursos motivacionais. Alimente-a com fatos.");
```
