---
id: "PV_KE_095"
title: "Role-Based View Isolation (Anti-Noise UX)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Implementation Phase"
  - "Execution Standards"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  - tension_with: "AN_KE_082 (Read Documentation Before Acting) vs Role-Based View Isolation"
    resolution: "Isolamento operacional (PV_KE_095) EXIGE visibilidade tática de contexto macro (AN_KE_082). Resoluçao: Breadcrumbs + Read-Only contextuais substituem poluição de campos. Role-based filtering passa à frente, mas com navegação enriquecida para acesso ao macro sem poluir a view local."
---

# PV_KE_095 - Role-Based View Isolation (Anti-Noise UX)

**Type:** Operator Interface Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:clickup-engineer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 15: Configurando o ClickUp para Sinkra / Passo 4]

## Purpose
Garantir a adoção do Sistema de Gestão SINKRA através do extermínio visual. Esta heurística (Commandment) declara que "Ruído é o Inimigo Número Um da Adoção Operacional". O Arquiteto jamais deve construir ou forçar os Executores a usarem "A View Genérica", que exibe a totalidade do Processo Master, campos de Pipeline, status de Automação de Infraestrutura e métricas C-Level tudo junto para um Operador de ponta que só precisa anexar um arquivo. Cada Executor (Account Manager, Editor, Gerente) OBRIGATORIAMENTE deve possuir uma *View Isolada Privativa* que filtre agressivamente tudo que for estritamente inútil para o andamento do seu Primitivo/Token ou Átomo no Sistema SINKRA.

## Configuration
```yaml
PV_KE_095:
  name: "Strict View UX Filtration"
  zone: "zone_0.8"
  trigger: "Fase 7 - Implementation. O Arquiteto ou ClickUp Engineer configura Painéis, Listas e Vistas Públicas no Software Base SINKRA (Ex: Monday, Jira, Notion)."
  evidence_threshold: "structural_logic"
  rule: |
    O Sistema Operacional Visual DEVE seguir o 'Role-Based Visibility Principle':
    - Visão Operador (Human): Mostra apenas Tokens e Átomos designados e prazos curtos. Nada de Meta-YAML. Oculta Configurações de Agente/Worker.
    - Visão Gerente: Mostra Agregação, Fluxos Bloqueados (VETOS) e Distribuição de Carga. NUNCA mergulha nos detalhes textuais menores do Executor de Fim de Linha em sua Board Diária Padrão.
    - Se a View causa cansaço visual, o Executor volta à Planilha. O Time perde o State Flow, o SINKRA morre de asfixia não-tática. A configuração Modular da Visão deve ser radical.
```

## Decision Tree
```javascript
IF (designing_Front_End_dashboards_or_Kanbans_for_the_Human_Team)
  STEP_1: EXAMINE the fields, columns, and tasks presented uniformly.
  STEP_2: ENFORCE strict filtration based on the Role Matrix (Phase 3).
    IF (An Audio Editor sees columns for "Meta_Quality_Score_Of_Campaign" or "Agent_System_Prompt_Link" or "C_Level_Approval_Flag")
      -> VETO: You are burying the Operator in Architectural Noise. Their screen should only contain: "Briefing", "Audio File", "Deadline", "Done Button". Hide all Master SINKRA fields behind 'Show More' or completely.
    IF (The Arquiteto creates distinct, locked views titled `View: Account Manager`, `View: Video Edit`, `View: Ops Director` with specific groupings and filters)
      -> ACCEPT: Operational harmony. The system adapts to the Role, the Role does not adapt to the Matrix complexity.
NEVER:
  Achar que transparência é jogar o SQL Inteiro da Empresa no FrontEnd para "todos verem". Em OPs de Alta Densidade (Centenas de Projetos por sprint), dados sem relevância local causam Paralisia de Análise. A Arquitetura Híbrida deve ser visível na Raiz (Phase 2), mas invisível no Campo (Phase 7).
```

## Failure Modes

### Misapplication / Excess: "O Silo Asfixiante Oculto (Anti-Contexto)"
- **Trigger:** A Equipe aplica o isolamento de forma tão ditatorial que o Operador (Editor de Vídeo, por exemplo) fica inteiramente cego de *Por Que* ou para *Onde* o Projeto vai. 
- **Manifestation:** O Operador vê a Task "Editar Video 3" mas não consegue acessar a Campanha Macro (Molecule), nem ver em qual Rede vai ser publicado na Tática, recebendo informações esquartejadas.
- **Detection:** Reclamações que a equipe virou uma "fábrica de botões apertados às cegas" onde não se consegue visualizar o Escopo Inteiro (O Big Picture) das Campanhas. O Engajamento morre.
- **Recovery:** A Lei do Isolamento do Ruído (PV_KE_095) suprime CAMPOS E ETAPAS TÉCNICAS INÚTEIS. Ela NÃO suprime o Alinhamento. É OBRIGATÓRIO fornecer ao Executor Humano, no escopo local, um Read-Only Path ou Contextual Description (Documentos Associados / Breadcrumbs / Clickable Parent Folders) que deem sentido Espacial Operacional (Contexto rico), permitindo "Zoom-Out Clicando no Link da Campanha" mas sem poluir o "Inbox Principal Deles" de colunas.

### Omission / Failure to Activate: "O Frankenstein Poluído"
- **Trigger:** A Equipe cria o Board do ClickUp ou Sistema Equivalente no "Padrão Nativo", e manda o Link Geral da "List Master" para as Equipes Operacionais Trabalharem no Dia 1 de SINKRA, sem criar Views ou Permissões.
- **Manifestation:** O Time abre o Software. Vê um Master Board Tático contendo 2.400 tasks com 38 Colunas Diferentes e Agrupadores Aleatórios, com Checkboxes Extraterrestres misturados ("Score_IA_Veto", "Retry_Status_N8N") e desiste. A adoção não vinga. O C-level culpa a ferramenta "complexa".
- **Detection:** Frequente exportação de dados pro MS Excel para o time "entender melhor e dividir nas Dailies". A morte lenta da Centralidade de Dados SINKRA.
- **Recovery:** Destruir a Exposição Livre. NENHUM MEMBRO não-master da Equipe deveria entrar (Default Board) no Board Principal Sem Filtros de um Processo Massivo (Organism/Instance level master view) sem um Filtro Rígido Pré-Salvo (`Me Mode`, `Role Mode`).

---

## Validation

**Paradoxo Identificado:** Isolamento visual vs. Consciência contextual.

A heurística resolve a tensão entre dois imperativos irreconciliáveis:
1. **Ruído = Morte de Adoção:** Excesso de informação paralisa operadores de ponta (fábrica de botões cegos).
2. **Cegueira = Desengajamento:** Isolamento radical sem alinhamento tático faz o executor perder o "Big Picture" (silo asfixiante).

**Resolução operacional:** O isolamento é sobre *campos e coluna técnicas inúteis*, não sobre *contexto funcional*. Breadcrumbs, navegação pai/filha e descrições contextuais em Read-Only permitem acesso ao macro sem poluir a view local do micro. O operador vê apenas seu Átomo/Token primário, mas pode clicar para entender em que Molécula/Campanha ele está inserido.

**Métricas de sucesso:**
- Redução em 80%+ de exportações para Excel para "entender melhor"
- Adoção Day-1 acima de 60% (sem treinamento extenso)
- NPS operacional (não-master users) >= 7/10
- Tempo médio de onboarding para novo role < 30 minutos

**Aplicabilidade:** Fase 7 (Implementation) em sistemas SINKRA com 50+ operadores simultâneos, 3+ roles distintos, e 500+ tasks/sprint. 
