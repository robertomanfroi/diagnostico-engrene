---
id: "PV_KE_072"
title: "A Dicotomia do Fim-de-Linha (Post-Condition vs Acceptance)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Standards"
  - "Validation Nodes"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Sequential Gate Architecture"
  resolution: "Segregate validation by processing orbit: fast/binary at exit node (post-conditions), qualitative/human at quality gate (acceptance criteria). Both must coexist but execute in separate substrates."
---

# PV_KE_072 - A Dicotomia do Fim-de-Linha (Post-Condition vs Acceptance)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 12: Campo 7: A Diferença Crítica]

## Purpose
Excluir debates amadores que arrastam automação ao poço lento da subjetividade emocional. A máquina (e a sanidade) depende da separação sagrada entre "Pós-Condição Geométrica Rápida" (Tá entre 0 e 10? Sim. Pode ir) e os "Critérios de Aceite de Negócios" (O valor entregue serve ao Universo Cliente com excelência relacional?). Os dois convivem, mas são processados por órbitas distintas. Post-conditions travam portas locais; Acceptance Criteria destravam portões maiores de Qualidade (Quality Gate). Morte a fusão dos dois.

## Configuration
```yaml
PV_KE_072:
  name: "Structural VS Value Validation Boundary"
  zone: "zone_0.8"
  trigger: "O Arquiteto submete ao Worker a exigência que no encerramento da tarefinha, ele decida por boolean se 'A qualidade criativa do Relatório superou métricas aceitáveis do nosso Marketing no Semestre passado'."
  evidence_threshold: "computer_science_axiom"
  rule: |
    SE uma Validação na extremidade de um Atom roda em 1 milisegundo baseada em Regex, Range Limit, Formatos ou Checklists Binárias Puras Claras,
    ENTÃO DEVE residir na casa `Post-Conditions` exigida pela Sintaxe pra encerrar a Subida Viva.
    MAS SE exige comparação de Performance Global, Opinião, Teste cego ou Estatística Evolutiva humana... ENTÃO é um `Acceptance Criteria` (Exige Escala Histórica/Validador de Clone superior/Quality Gate isolado subseqüente).
  veto_condition:
    trigger: "Pausar um Job Cron de Limpeza Simples Rápida para emitir requesições externas de aprovação qualitativa sem fundamento formal restrito, congelando as Tasks Simples em Review Loopings bizarros."
    action: "VETO PROCEDURAL. Condição binária responde à Si mesma rapidamente. Pare de tentar atirar sentimentos corporativos no pescoço de Atoms."
```

## Decision Tree
```javascript
IF (writing_the_end_exit_rules_for_a_process_unit)
  STEP_1: EXAMINE your validation phrase.
    IF (Validation == 'Score is Type<Int> & Inside Array[A, B, C]')
      -> This is a POST-CONDITION. Give it to the local automatic Worker node. It executes 10.000 times a minute automatically and bounces failures fast.
    IF (Validation == 'Conversion rate improved over last week's median by 5% with similar audience sentiment on X_Twitter metrics.')
      -> This is ACCEPTANCE CRITERIA. Strip it from the atomic exit lock and allocate it into a Macro Molecule QUALITY GATE powered by Analysis Agents/Humans.
NEVER:
  Confundir o fiscal mecânico alfandegário com o crítico literário avaliador de Ouro de Prêmio Nobel, entupindo a catraca inicial com o cara errado.
```

## Failure Modes

### Misapplication / Excess: "O Império das Máquinas Frias Puras (Omissão de Aceite)"
- **Trigger:** Num acesso de adoração a sistemas ultra-rápidos determinísticos e céticos (Lógica Computacional Pura), a Equipe de Dados extermina os QA Gates abstratos longos argumentando ser "ineficiência operacional de RH" usando Post-Conditions duras em tudo. 
- **Manifestation:** Textos de blog absurdamente robóticos passam voando pois "atingiram +800 Palavras e continham H1, H2 e links (Passou as Post-Conditions Fáceis!)". Contudo, as taxas brutais de Desinscrição dos Leads por acharam o conteúdo asqueroso arruinam as list-bases corporativas e o CTR no chão.
- **Detection:** Entregas rápidas aos montes. Nenhum impacto, zero coração comercial, clientes desanimados gerando Churn e devoluções nos contratos pois "passou teste de sintaxe e quebrou teste de Alma SINKRA".
- **Recovery:** A Restauração do Equilíbrio e da Lógica. Post-Conditions seguram as pernas dos cavalos; Acceptance Criteria direcionam o caminho para a Guerra.
- **Prevention:** Obrigar Handoffs Qualitativos de Organismos vitais passarem sob esquadrões de Clones bem afinados em Sentimento, não só em Regex.

### Omission / Failure to Activate: "A Frouxidão Semântica Mágica"
- **Trigger:** Configuram "O Texto tem que estar bom" direto pro Claude ou ChatGpt resolver via Prompts. Não definem nenhuma checagem final dura Binária que assegure Formato (`É JSON Exato válido? É String Limpa sem Aspas Erradas?`).
- **Manifestation:** O ChatGpt responde "Ok amigo, aqui está o texto bem bonito..." misturado com chaves abertas de Códificação que, ao cruzar o pipeline em Handoff e encostar no Banco de Dados Estruturado, Crasham violentamente estourando 40 APIs simultâneas por injeção suja ou má formatação elementar. O Agente mandou algo "ótimo pro marketing" mas "horripilante pro interpretador backend". 
- **Detection:** Falhas crônicas de sintaxe nos conectores dos Organismos que quebram o pipeline "sem motivo".
- **Recovery:** Todo Atom sem exceção TEM post-conditions binários estruturais cruéis, secos e intransigentes. Sem eles, o esgoto verbal é perigosamente envenenado dentro do Sistema e aceito como Data Lake por tolerância ingênua.

---

## Validation

✅ **Paradox Identified:** The simultaneous need for deterministic/fast validation (post-conditions) vs. qualitative/sentiment-based validation (acceptance criteria) creates an irresolvable tension if collapsed into one gate.

✅ **Tension Resolution:** Orbit separation — post-conditions execute at the atomic exit node (milliseconds, binary, regex-based); acceptance criteria escalate to a distinct Quality Gate layer (human/agent review, historical context, qualitative signals).

✅ **Application Guard:** Use this heuristic to veto any proposal that attempts to merge post-condition checks (fast, local) with acceptance criteria (slow, distributed, opinion-bearing) into a single validation point. Separation of concerns saves velocity and credibility.
