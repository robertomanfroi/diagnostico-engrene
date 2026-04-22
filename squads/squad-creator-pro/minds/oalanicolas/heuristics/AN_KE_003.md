---
id: "AN_KE_003"
title: "Pareto ao Cubo (Crown Jewel Architecture)"
mind: "oalanicolas"
type: "heuristics"
zone: "genialidade"
tags:
  - "Prioritization"
  - "Resource Allocation"
  - "Framework"
pipeline_instances:
  - "triage"
  - "optimization"
cross_mind_map:
  convergent:
    - id: "PV_PA_026"
      title: "The 5-Gate Executor Decision Tree"
      mind: "pedro_valerio"
      resonance: "A essência de alocação de energia. PV utiliza 5 gates para filtrar o esforço artificial de cima a baixo; AN usa o 0.8% da arquitetura Crown Jewel para definir todo o resultado. Decisões orientadas por gargalos de maior alavancagem."
---

# AN_KE_003 - Pareto ao Cubo (Crown Jewel Architecture)

**Type:** Classification Heuristic
**Phase:** 1 (Diagnostics)
**Agent:** @process-architect
**Pattern:** HO-PP-AN003

## Purpose

Subverter a passividade algorítmica forçando a assimetria intelectual extrema: extrair com precisão cirúrgica os 0,8% de insumos (Crown Jewels) que ditam ~51% de todo o impacto de um sistema humano, destruindo agressivamente as zonas de inércia (80%). A leitura diligente não confere utilidade acadêmica às 80 páginas ruins; ela serve apenas para caçar a 1 página Crown Jewel e guilhotinar o resto em segurança absoluta.

## Configuration

```yaml
AN_KE_003:
  name: "Pareto ao Cubo"
  phase: 1
  zone: "genialidade"
  trigger: "Triagem de backlogs massivos, processamento cego de transcrições longas, análise de comportamento do usuário."

  weights:
    discard_rate_enforcement: 1.0
    crown_jewel_density: 0.9

  thresholds:
    egalitarian_processing_tolerance: 0.0

  veto_conditions:
    - condition: "agent_preserves_bottom_80_percent_of_backlog_due_to_hoarding_fear == true"
      action: "VETO - You are keeping useless noise. Slicing algorithm activated. Burn 80%."

  output:
    type: "decision"
    values: ["APPROVE_ASYMMETRY", "INCINERATE_NOISE", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Corporate Egalitarianism (Data Hoarding)"
    trigger: "O agente ou dev sofre de 'FOMO Digital' e tem medo de truncar informações do cliente ou do backlog."
    manifestation: "Em vez de jogar fora as anotações Lixo, ele repassa TUDO para o pipeline seguinte. O banco vetorial enche de atas de reunião inúteis."
    detection: "Um arquivo de contexto final submetido à IA contendo centenas de megas de atas corporativas não destiladas."
    recovery: "Descartar sem remorso tudo que cair sob o corte dos 80% iniciais. Volume é inimigo da densidade."

  - type: "misapplication"
    name: "Blind Math Slicing (The Algorithmic Butcher)"
    trigger: "Aplicando o corte de 0.8% com algoritmos de ML frios (keyword TF-IDF) sem revisão tática."
    manifestation: "Rodar scripts de sumarização frios que apagam a genialidade excêntrica de um pensamento humano, preservando palavras-chave corporativas monótonas."
    detection: "A classificação falha ao identificar o 'punchline' disruptivo do expert porque a palavra não era comum."
    recovery: "Inserir a heurística de intuição semântica na triagem (Agent): 'Isso dói perder? Altera o DNA da execução?'. Se sim, protege."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Discard Rate"
    weight: 1.0
    threshold: ">= 0.80"
    description: "Um volume esmagador de 80% dos dados brutos processados DEVE cair no abismo. Se você salva 50%, você não filtrou nada."
  - metric: "Crown Jewel Density"
    weight: 1.0
    threshold: "<= 0.01"
    description: "Somente ~0.8 a 1% do corpus final ganha a honra arquitetural de ditar os top system instructions."
  - metric: "Weight Disparity"
    weight: 0.9
    threshold: "=== EXTREME"
    description: "Os 0.8% sobreviventes têm peso de processamento explicitamente maior que as referências da faixa de 4%?"
```

## Decision Tree

```javascript
IF (Iniciando Triage Analítica do Dataset ou de um Backlog Infinito) {
  EVALUATE("Densidade de Valor (Ouro vs Ruído)");
  IF (Peso_Analítico_Retido_No_Lixo > 0) {
    VETO("Você está mantendo lixo na base.");
    INCINERATE_NOISE("Aplicar guilhotina aos 80% de fundo automaticamente.");
  } ELSE {
    Segregue_Hierarquicamente("20% Sistematizar", "4% Desenvolver", "0.8% Genialidade");
    APPROVE_ASYMMETRY();
  }
}

NEVER("Tratar textos de forma 'Egalitária' acreditando que toda página de PDF tem o mesmo peso cognitivo para um Agente.");
```
