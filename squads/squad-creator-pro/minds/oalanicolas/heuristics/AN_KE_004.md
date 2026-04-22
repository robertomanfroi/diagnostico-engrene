---
id: "AN_KE_004"
title: "Regra do Ouro (Source Curation)"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Curation"
  - "Quality Gate"
  - "Extraction"
pipeline_instances:
  - "data-curation"
  - "rag-indexing"
cross_mind_map:
  convergent:
    - id: "PV_PA_022"
      title: "Primary Validation Coupling (No Auto-Validation)"
      mind: "pedro_valerio"
      resonance: "Ambos combatem a corrupção orgânica de dados por falta de âncora à fonte. AN pune agentes que distorcem o texto primário durante curação; PV acopla qualquer verificação final de AI aos repositórios primários invioláveis."
---

# AN_KE_004 - Regra do Ouro (Source Curation)

**Type:** Classification Heuristic
**Phase:** 2 (Atom Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN004

## Purpose

Blindar o clone cognitivo contra a doença infecciosa da "Media Training". Impor um filtro que impeça letalmente que palestras corporativas engessadas ou declarações de Relações Públicas contaminem o DNA da mente com ruído institucional, forçando a busca pela verdade revelada no improviso duro, nas trincheiras e no Q&A não roteirizado.

## Configuration

```yaml
AN_KE_004:
  name: "Regra do Ouro"
  phase: 2
  zone: "excelencia"
  trigger: "Avaliação pré-processamento de um PDF/Vídeo/Áudio candidato a compor a Base Vetorial (RAG) do Clone."

  weights:
    trench_improvisation_ratio: 1.0
    pr_filter_strictness: 1.0

  thresholds:
    scripted_media_dilution: 0.2 # MAX 20% PR Material allowed

  veto_conditions:
    - condition: "corpus_volume_dominated_by_scripted_keynotes == true"
      action: "VETO - Diluição Identitária. A carga de Bronze macio superou o lastro de Ouro duro."

  output:
    type: "decision"
    values: ["APPROVE_GOLD_SOURCE", "TAG_AS_BRONZE", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "The False Prophet Flow (The Coward)"
    trigger: "O programador cede à preguiça de extrair e transcrever vídeos longos sem legenda."
    manifestation: "Ele insere no RAG as 5 primeiras palestras em palco do YouTube, ignorando material pesado de 4 horas de mentoria fechada."
    detection: "O Clone Mental passa a responder a problemas cirúrgicos de forma genérica, emitindo frases motivacionais e bullets abstratos."
    recovery: "Limpar a base de dados dos pitches de vendas e inserir as mentorias de 3 horas em call privada. Exclua a 'Voz do Palco'."

  - type: "misapplication"
    name: "Anti-Intellectualism (The Zealot)"
    trigger: "Descartar manifestos ou livros oficiais extremamente rigorosos pelo autor apenas por 'não serem um vlog cru espontâneo'."
    manifestation: "Desprezar frameworks absolutos do expert (seu Playbook oficial de vida) simplesmente pela presença de revisão editorial."
    detection: "Excesso crônico de ideias brilhantes em improviso, mas total ausência de Arquiteturas de Base estruturadas para o RAG se apoiar organizadamente."
    recovery: "Restituir livros/artigos de tese central como 'Ouro Conceptual Sistêmico'. Improviso traz a tática, Livros trazem a Mola-mestra."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Improvisation Ratio"
    weight: 1.0
    threshold: ">= 0.60"
    description: "Mais de 60% das fontes valiosas devem advir primariamente de contextos de Q&A agressivo, mentorias fechadas, reuniões vazadas ou discussões > 2hrs."
  - metric: "PR Pollution Limit"
    weight: 1.0
    threshold: "<= 0.20"
    description: "Fontes de palco roteirizadas e discursos pasteurizados compõem uma minoria inofensiva ou nula?"
  - metric: "Framework Baseline"
    weight: 0.9
    threshold: "=== TRUE"
    description: "O 'Ouro Formal' (Livro de fundação do autor) atua como baliza central do improviso?"
```

## Decision Tree

```javascript
IF (Agente/Dev Ingestando Base de Dados) {
  EVALUATE("Taxonomia de Autenticidade ('Palco' vs 'Trincheira')");
  IF (Composição_Roteirizada_PR > 0.20) {
    VETO("Excesso crônico de Media Training no LLM Context. Pasteuring effect detected.");
    TAG_AS_BRONZE("Relegar arquivos a pesos mínimos de prioridade Vetorial.");
  } ELSE IF (Material exibe vulnerabilidade e improviso tático) {
    APPROVE_GOLD_SOURCE("Executar Deep Extraction.");
  }
}

NEVER("Jamais aprovar um Handoff que mistura Ouro (Mentoria) e Bronze (Palco) cegamente no mesmo chunking weight.");
```
