---
id: "PV_KE_086"
title: "The AS-IS First Commandment (Discovery Fallacy)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Discovery Phase"
  - "Execution Standards"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Depth-First Sequential Investigation"
  resolution: "Prioritize structural dependencies (who-approves-what) over granular detail; iterate only on data that blocks Phase 2 Architecture"
---

# PV_KE_086 - The AS-IS First Commandment (Discovery Fallacy)

**Type:** Analytical Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:process-mapper
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 14: Fase 1 - Discovery]

## Purpose
Impedir a Morte Epistêmica na fase de mapeamento (Fase 1: Discovery). O erro mais caro de qualquer projeto corporativo é documentar a "intenção do processo" (TO-BE, como o gestor ou diagrama antigo acham que é) em vez da "realidade física do processo" (AS-IS, como efetivamente roda nas sombras, nas planilhas piratas e nos puxadinhos do WhatsApp). Esta heurística proíbe terminantemente qualquer otimização, futurologia ou juízo de valor na Fase 1. A Discovery é um diagnóstico FOTOGRÁFICO, duro e imparcial, de "como é", inclusive (e principalmente) se o processo atual for uma catástrofe institucionalizada. Você não pode redesenhar aquilo que você não conhece.

## Configuration
```yaml
PV_KE_086:
  name: "Ruthless AS-IS Mirroring"
  zone: "zone_0.8"
  trigger: "Durante a execução da Fase 1 (Discovery), ao documentar o mapa do processo, levantar stakeholders ou relatar passos executivos de um domínio."
  evidence_threshold: "direct_observation"
  rule: |
    Na Fase 1, TODO relato de diretor ou documento legado DEVE ser rebaixado à categoria de "Hipótese de Intenção Documentada".
    A verdade é extraída EXCLUSIVAMENTE de entrevistas rigorosas com os EXECUTORES FINAIS ou da observação direta (Data Traces) dos artefatos.
    - Se o Diretor jura que a etapa B segue a Etapa A.
    - Mas a Planilha mostra que a Coordenadora, 3x por semana, ignora a Etapa A.
    - O Process Map Oficial (AS-IS) da Fase 1 GRAVARÁ a gambiarra da Coordenadora e não o diagrama limpo do Diretor.
    A Fase 1 coleta; o TO-BE só acontece na Fase 2 (Architecture). O Mapeador é Câmera, não Arquiteto.
```

## Decision Tree
```javascript
IF (mapping_a_business_process_in_Phase_1)
  STEP_1: INTERVIEW the direct executor, NOT the manager.
  STEP_2: CAPTURE exactly what happens.
    IF (Executor states: 'I manually copy this PDF data into the system every Friday, because the integration breaks.')
      -> ACCEPT: Document the manual duplication as the canonical Step X.
    IF (Manager states: 'Our CRM automatically syncs the data on Fridays.')
      -> REJECT: Label as 'Aspirational TO-BE'. Retain the actual manual reality.
NEVER:
  Acreditar que o Fluxograma Institucional é um processo. O Fluxograma Institucional usualmente data de 2 anos atrás e esconde os atalhos diários criados por desespero operacional pela base. A Fase 1 exige o mapa do desespero vivo, não a utopia engavetada.
```

## Failure Modes

### Misapplication / Excess: "Investigação Paralisante e Subversiva"
- **Trigger:** O Mapeador usa a heurística para forçar inquéritos tão granulares e hostis na operação ("Mas qual mão você usa pra digitar a célula A1?") que o mapeamento dura semanas para coisas irrelevantes.
- **Manifestation:** O mapeador se recusa a compilar fluxos básicos operando uma espécie de auditoria policial paralisante contra todos os gestores, quebrando pontes sociais e demorando demais para chegar à fase de Arquitetura.
- **Detection:** Reclamações que a fase de Discovery estourou a margem de 4 horas estipuladas e virou uma auditoria financeira de semanas sobre coisas cujo desvio já foi notado.
- **Recovery:** A Fase 1 mapeia o Fluxo de Valor AS-IS macro, estrutural. O Diagnóstico Fotográfico é para achar os nós corrompidos no processo real (quem aprova o quê de verdade?), e não compilar logs de digitação de cada analista. Discovery em SINKRA dura em média 2 a 4 horas. Seja afiado, colete as ramificações ocultas cruciais, e avance.

### Omission / Failure to Activate: "A Síndrome de Estocolmo do Fluxograma (Wishful Thinking)"
- **Trigger:** O mapeador tem preguiça, agenda reunião só com a Alta Gerência, recebe um PDF limpo com Setinhas Coloridas desenhadas pela agência há 3 anos atrás e carimba aquilo como o `process_map_final`. 
- **Manifestation:** O Arquiteto recebe uma ficção na Fase 2. Todo o design subsequente (Atribuição, Workflows, Qualidade) será desenhado com perfeição axiomática... em cima de um processo imaginário. Quando rodar em produção na Fase 7, a operação explode porque 12 etapas gambiarra críticas do mundo real ficaram fora do mapa e ninguém fará elas. O sistema para.
- **Detection:** O Processo desenhado na SINKRA "trava" o cliente ou a operação no primeiro mês porque o Worker ou o Agent ignora as contingências ocultas da Cultura, o que leva os executores a fazerem as coisas por fora de novo, abandonando a plataforma.
- **Recovery:** A Lei da Observação Direta. Discovery obriga rastrear dependências reais (Logs de Sistema, Histórico de Commits e Chats) e as entrevistas sempre descem ao nível "Chão de Fábrica" para a Extração de Realidade. Se a descoberta violou isso, zere e repita.

## Validation

✓ **Paradox Recognized:** Photographic accuracy (unlimited investigation) vs. pragmatic time-boxing (4-hour Discovery gate) create inherent tension.

✓ **Resolution Encoded:** Prioritize structural critical paths (approval chains, data handoffs, blocking dependencies) and defer cosmetic detail to Phase 2 Architecture.

✓ **Field Verified:** Heuristic activates only when Phase 1 executor mapping is underway; safeguard prevents unlimited rabbit-holes while preserving epistemic integrity of AS-IS capture.
