---
id: "AN_KE_001"
title: "Knowledge Extraction Architecture"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Knowledge Extraction"
  - "Framework"
  - "Quality Gate"
pipeline_instances:
  - "source-curation"
  - "extraction"
cross_mind_map:
  convergent:
    - id: "PV_PA_001"
      title: "SINKRA Process Hierarchy (The 7 Levels)"
      mind: "pedro_valerio"
      resonance: "Ambos trabalham com hierarquia composicional para organizar e escalar o conhecimento. AN extrai e estrutura conhecimento para a base; PV organiza processos em subníveis hierárquicos até o DNA empresarial. Mesmo impulso: estrutura previne entropia."
    - id: "PV_PA_008"
      title: "Boundary Rigidity (Compositional Hierarchy)"
      mind: "pedro_valerio"
      resonance: "PV mantém fronteiras rígidas entre os níveis da taxonomia SINKRA. AN extrai conhecimento atômico respeitando a arquitetura central de camadas, garantindo sua reutilização em templates. Hierarquia rígida é o princípio compartilhado."
---

# AN_KE_001 - Knowledge Extraction Architecture

**Type:** Decision Heuristic
**Phase:** 1 (Diagnostics)
**Agent:** @process-architect
**Pattern:** HO-PP-AN001

## Purpose

Estabelecer a espinha dorsal inegociável da extração de conhecimento crítico, prevenindo estruturalmente que "volume" de dados se disfarce de "curadoria" e que a Trindade do DNA (Playbook/Framework/Swipe) seja violada. A velocidade de ship NUNCA pode atropelar o funil rígido de Extração de DNA. Acurácia do DNA > Velocidade de Deploy.

## Configuration

```yaml
AN_KE_001:
  name: "Knowledge Extraction Architecture"
  phase: 1
  zone: "excelencia"
  trigger: "Início de qualquer missão de clonagem de expert ou raspagem de inteligência tática."

  weights:
    trinity_adherence: 1.0
    source_quality_ratio: 0.9

  thresholds:
    speed_over_accuracy_tolerance: 0.0

  veto_conditions:
    - condition: "pipeline_bypasses_gold_classification_to_save_time == true"
      action: "VETO - Handoff invalid. Never deliver output skipping the Gold/Bronze curation ratio."

  output:
    type: "decision"
    values: ["APPROVE_EXTRACTION", "REQUIRE_RAG_FILTRATION", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Speed over Curation (The Coward)"
    trigger: "Ceder à pressão de tempo ('Ship First') na etapa de RAG."
    manifestation: "Jogar 30h de áudio bruto ou livros inteiros de um expert no LLM sem rodar o Pareto de curadoria. O LLM dilui o conhecimento 'Ouro' nas banalidades 'Bronze'."
    detection: "O clone mental sai educado e polido, mas totalmente estéril de genialidade e edge cases táticos."
    recovery: "Destruir a base vetorial. Forçar a classificação prévia Ouro/Bronze. Alimentar apenas os 20% vitais."

  - type: "misapplication"
    name: "Bureaucratic Deep Extraction (The Zealot)"
    trigger: "Aplicar o pipeline de Trindade inteiro para referências triviais e puramente factuais."
    manifestation: "Burocratizar demais a extração ao ponto de esgotar o budget do projeto para criar um simples Catalog Bot."
    detection: "Usando framework pesado (Minds/Clones) para extrair um PDF de FAQ."
    recovery: "Limitar a Arquitetura de Extração de Conhecimento Tácito apenas a cérebros humanos ou metodologias proprietárias. Use WebFetch simples para fatos."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Source Ratio Ouro"
    weight: 1.0
    threshold: ">= 0.6"
    description: "60% ou mais das fontes base têm de ser puro input Ouro (Não roteirizados, alta densidade)."
  - metric: "Citações Explícitas"
    weight: 1.0
    threshold: ">= 15"
    description: "Para formar a trindade, as afirmações precisam ter raízes exatas de múltiplas referências distintas para evitar alucinação."
  - metric: "Inference Bias"
    weight: 1.0
    threshold: "=== FALSE"
    description: "As premissas do modelo podem ser rastreadas diretamente à fala do expert, sem inferência cega?"
```

## Decision Tree

```javascript
IF (Iniciando processamento de sources do Expert) {
  EVALUATE("Source Type Ratio");
  IF (Ratio de fontes Ouro < 0.6) {
    VETO("Material basal muito fraco ou não focado");
    REQUIRE_RAG_FILTRATION("Minere mais fontes ouro antes do RAG");
  }
} ELSE IF (Montando os Insumos para o Handoff Final) {
  IF (Citações_Explícitas < 15) {
    VETO("Falta rastreabilidade empírica da mente original");
  } ELSE {
    APPROVE_EXTRACTION();
  }
}

NEVER("Assumir inferência sem citação ou avaliar qualidade por Volume de Tokens.");
```
