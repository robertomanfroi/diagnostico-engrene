---
id: "PV_KE_057"
title: "O Limite da Iteração Cíclica (The Iteration Cap in Controlled Loops)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Iterative Constraints"
  - "System Resilience"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_042 (A Falácia da Variância Zero — Six Sigma vs Agent Adaptation)"
  resolution: "Segment by task type: Artistic tasks need flex loops (≥3 iterations), Data/Math tasks need rigid loops (=1 or go/no-go). Balance max_iterations per domain, not globally."
---

# PV_KE_057 - O Limite da Iteração Cíclica (The Iteration Cap in Controlled Loops)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 8: Organism 8: Controlled Loop]

## Purpose
Estancar o ralo gravitacional das revisões contínuas e silenciosas. Num processo que requer ciclos e ajustes, a ausência de um "Teto de Iterações" permite a deterioração de energia mental, desgaste de tempo e a incapacidade de sinalizar que "se chegou na vez 5 sem resolver, o problema não é o ajuste, o problema é a base original da tarefa!".

## Configuration
```yaml
PV_KE_057:
  name: "Iteration Cap on Controlled Loops"
  zone: "zone_4"
  trigger: "Configurando fluxos de 'vai-e-vem' como revisões de design, melhoria de copy, testes QA de software, conversas de feedback."
  evidence_threshold: "process_hygiene_axiom"
  rule: |
    SE o pipeline possui um Organismo de Tipo `Controlled Loop` (Ciclo Iterativo para busca de Convergência Qualitativa/QA Gate)
    ENTÃO OBRIGATORIAMENTE deve possuir uma Constante `max_iterations: N`. 
    Ao perfurar esse teto sem solução > Acionar Action Escalonada.
  veto_condition:
    trigger: "Um Design ou dev cycle que tem um Status 'Em Revisão', voltando livremente quantas vezes a mente humana quiser."
    action: "VETO DE CICLO MORTO. O processo deve contar e matar tentativas esgotadas forçando escalonamento."
```

## Decision Tree
```javascript
IF (building_a_feedback_loop_between_executors)
  STEP_1: DEFINE the Quality Gate failure condition.
  STEP_2: SET `max_iterations` counter (e.g., = 3).
  STEP_3: MONITOR every failed Quality Gate.
    IF (iteration_count < max_iterations)
      -> ACCEPT: Send it back for standard revision.
    IF (iteration_count == max_iterations)
      -> REJECT LOOP: Do not iterate. Intervene! Escalate to higher authority/strategist. 
      -> REASON: The loop is structurally compromised.
NEVER:
  Acreditar que a 7ª "alteração só na barrinha de baixo do layout" resolverá magicamente o conceito fracassado no briefing original.
```

## Failure Modes

### Misapplication / Excess: "O Loop de Morte Precoce"
- **Trigger:** Fixar iterativas máximas igual a N=1 em ambientes altamente fluidos ou artísticos/criativos. 
- **Manifestation:** O primeiro erro de digitação de um IA ou primeiro rascunho de um humano inexperiente gera um disparo de P0 alertando toda a C-suite que o processo de Design inteiro quebrou. 
- **Detection:** Reclamação dos Diretores de que a operação exige atenção excessiva e prematura à qualquer soluço da execução criativa.
- **Recovery:** Balancear o `max_iterations`. Uma taxa normal na operação SINKRA gira em 3. Dar "chance de ar puro" para a simbiose e refinamento operar de forma local no seu núcleo original antes de jogar a bomba superiormente.
- **Prevention:** Tarefas Artísticas precisam de Loop Flex (>= 3). Tarefas Matemáticas / Dados Físicos precisam de Loop Rígido (=1, ou funciona, ou não vai pro ar).

### Omission / Failure to Activate: "O Pêndulo Infinito (Death by a Thousand Cuts)"
- **Trigger:** Processos onde a iterabilidade é puramente guiada pelo desgaste (Ex: "Vai refazendo aí pra gente ver").
- **Manifestation:** Em Dezembro de 2026, três desenvolvedores continuam trocando mensagens de 5 parágrafos ou refazendo a mesma PR com um Designer, 17 edições depois, não entregando Valor Comercial. O time desanima e ambos sentem que o outro é incompetente. O Sprint apodrece na coluna de QA.
- **Detection:** Anos envelhecendo e "Refazer/Aprovação Adiada" constantes na mesma thread do Slack/ClickUp.
- **Recovery:** Teto de Iteração Rígido inserido. Estourou? Break. Elevação e resolução no nível Sênior/CTO.
- **Prevention:** Bloqueio Lógico no Board. Uma task que bata o limite de Reject no nó ganha cor vermelha e os Executores bases perdem o poder de enviá-la novamente sem a rubrica de desbloqueio do Product Owner (Desbloqueio via re-briefing obrigatório).

## Validation

✓ **Paradoxo Identificado:** A heurística resolve a tensão entre permitir iterações necessárias e evitar loops infinitos através da segmentação contextual — tarefas criativas recebem tolerância iterativa maior, enquanto tarefas determinísticas recebem tetos rigorosos.

✓ **Aplicabilidade:** PV_KE_057 valida-se em pipelines com `Controlled Loop` organism type. Deve estar mapeada em `squads/sinkra-squad/data/process-mapping-rules.yaml` como rule_trigger para QA gates.

✓ **Coesão:** Conecta com PV_KE_043 (Complexity Segmentation) e PV_PA_038 (Process Maturity Thresholds) através do princípio de diferenciação por domínio.
