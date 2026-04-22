---
id: "PV_KE_071"
title: "O Grafo Pelo Destino (Data Path Topology)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Orchestration Hierarchy"
  - "Data Governance"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  - tension_with: "PV_KE_054"
    resolution: "Determinismo absoluto (Saída→Origem obrigatória) vs. economia prática (variáveis de contexto para tarefas atômicas mínimas). Resolver: aplicar persistência estrutural apenas quando valor > custo, usar RAM para transições microscópicas."
---

# PV_KE_071 - O Grafo Pelo Destino (Data Path Topology)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 12: Campo 5: Saídas — e a intersecção Mágica]

## Purpose
Decifrar o código genético escondido atrás da ligação orgânica das engrenagens Atômicas SINKRA: a ordem de execução nunca é uma mera sequência temporal abstrata ("Seta Mágica: Faça B após A"). Ela só detêm integridade se orquestrada pelo *Cordão Umbilical do Campo de Destino/Origem*. O "Destino" declarado no Post-Saída da Tarefa A se traduz simultaneamente na exigência matemática da "Origem" (Entrada) da Tarefa B. Esse fluxo materializa um Grafo DAG invisível natural, unindo moléculas de maneira inexorável.

## Configuration
```yaml
PV_KE_071:
  name: "Destination to Origin Flow Construct"
  zone: "zone_0.8"
  trigger: "O arquiteto liga duas caixas de execução mas esquece de ligar a tubulação de transição dos arrays numéricos e textos que saem de uma e entram na outra."
  evidence_threshold: "computer_science_axiom"
  rule: |
    SE você declarar que a Task B é downstream da Task A,
    ENTÃO OBRIGATORIAMENTE um pedaço físico de Dados (Payload/Saída) da Task A [ex: `banco_qualificacoes.logs`] DEVE SER listado inequivocamente na porta do Campo 4 (Origem) da Task B.
    Dependência sem alimentação é mágica. SINKRA exige fluxo termodinâmico físico.
  veto_condition:
    trigger: "Tentar sequenciar tarefas e orquestrar fluxos onde a primeira gera um Arquivo X no S3 AWS, e a Tarefa B inicia dizendo no painel que seu Source é o iCloud Pessoal."
    action: "VETO DE INCOMPATIBILIDADE DE GRAFO. Se o cano despejou na caixa Alpha, a Mangueira tem que sugar de Alpha pra continuar adiante. Aborta execução via Validador Semântico de Fluxos."
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Grafo Determinístico Sequencial"
```

## Decision Tree
```javascript
IF (constructing_a_flow_between_multiple_independent_atomic_tasks)
  STEP_1: REVIEW Task A OUTPUT definitions (Variables, Types, Storage Links).
  STEP_2: REVIEW Task B INPUT Definitions immediately after it.
    IF (Task B claims its origin is [Slack/DM] while Task A clearly sent its output logic to [DataLake/GCS])
      -> REJECT. "The chain is broken. The graph physically snaps. Agent B will starve or hallucinate because inputs are missing in its assigned source."
    IF (The Outputs of A match perfectly the Origins of B implicitly through global store links)
      -> ACCEPT: Data Path topology secured physically.
NEVER:
  Supor que um Worker Autônomo ou Agente SINKRA tem visão onisciente para "adivinhar" que o resultado do processo anterior, por algum erro místico humano, foi largado na pasta "Downloads" do Windows em vez do Database. O Destino precisa ser explícito 
```

## Failure Modes

### Misapplication / Excess: "O Canudinho Inquebrável da Restrição Mental (Pipes Rígidos)"
- **Trigger:** Num acesso neurótico, o time de engenharia desenvolve uma arquitetura fechada onde absolutamente todo Micro-Atom isolado *PRECISA*, por lei, gerar um Objeto Físico Blob imenso em S3 Bucket, mesmo para tarefas abstratas mínimas de Ping/Notificação, gerando custos milionários com transações S3 IN/OUT Inúteis na nuvem.
- **Manifestation:** Tarefas microscópicas (Mandar "OK") são soterradas ao tentar forçar a regrinha dos 8 Campos para criarem "Dados Absolutos em Servidores" inflando as memórias da companhia sem gerar Business Value.
- **Detection:** Constatação em faturas da AWS ou Supabase com 50 milhões de acessos GET/PUT inúteis onde o Payload transitava em meros States ou Contextos em RAM que não demandavam Persistência Estrutural tão dramática.
- **Recovery:** Os "Destinos/Origens" de Tarefas Atômicas não precisam residir perpetuamente na Base de Dados Histórica Dura. Use Variáveis de Sessão ou de Workspace (Tokens) como campos locais temporários para amarrar nós microscópicos (e.g. `memory.context.result`).
- **Prevention:** Aplicar persistência atômica com parcimônia, usando variáveis ambientais onde tolerável. 

### Omission / Failure to Activate: "O Arquivo no Zip de Ninguém"
- **Trigger:** A Equipe Design roda seu Agent Atômico; eles fazem peças gráficas belíssimas; elas vão parar magicamente nos relatórios. Um mês depois, ninguem sabe o link original dos PNGs em Alta Resolução gerados no caminho.
- **Manifestation:** O Agente de Geração concluiu a sua Parte `Saída: Imagem` porém apontou que o `Destino = Workspace Local (Desktop Fantasma)`. Na sequência, um Head Criativo humano que era o Próximo Elo, olhava a tela compartilhada no dia, viu que era bonita, falou "Show Continua Bota no Site" - cortaram o cano físico de transferência e o registro não foi estocado com Link Limpo para o futuro. Quando o site cai e perdem o link, cadê a mídia crua? Morreu na instância em Branco.
- **Detection:** Solicitações constantes no time "Gente, onde vocês puseram aquele arquivo da Tarefa de Sexta...?"
- **Recovery:** Varredura. Qualquer Atom/Molecules sem "Persistido: True & Destino Explicito" são falhas procedimentais perigosas e deveriam levantar uma Flag de auditoria na compilação do processo mestre.

---

## Validation

✓ **Paradoxo Identificado:** Determinismo Absoluto vs. Economia (vide sys_tension acima)
✓ **Teste:** PV_KE_071 valida grafos DAG via contrato Source/Destination explícito
✓ **Aplicabilidade:** SINKRA Composição (Campos 4-5) + Orquestração Atômica
✓ **Status:** Operacional para arquiteturas enterprise; usar discretamente em microsserviços
