---
id: "PV_KE_063"
title: "A Obrigatoriedade do Arquivo Morto (Archiving COMPLETE Instances)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "System Hygiene"
  - "Data Governance"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_061 (O Axioma da Métrica Inerente) vs Visibilidade Operacional Reduzida"
  resolution: "Archiving: move to cold storage (preserved, not deleted) while removing from live operational view"
---

# PV_KE_063 - A Obrigatoriedade do Arquivo Morto (Archiving COMPLETE Instances)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 10: Anti-Pattern 4: Não Arquivar Instances Completas]

## Purpose
Preservar o fluxo neuro-visual da empresa impedindo que o "Sinal" de trabalho vivo seja afogado no oceano raso de trabalho conquistado passado. Instâncias velhas terminadas não merecem espaço poluidor no Dashboard principal. Elas transacionam em automático para `ARCHIVED` (Estado Frio em Deep Storage), mantendo a base viva e responsiva focada APENAS em sangrias, tráfegos e aprovações do tempo presente.

## Configuration
```yaml
PV_KE_063:
  name: "Archiving COMPLETE Instances"
  zone: "zone_4"
  trigger: "Se a visualização do gestor (Trello, Jira, Notion DataBase, Slack) mantiver cartões inativos que terminaram a 2 semanas entupindo e sujando a vertical da área principal ou da tag."
  evidence_threshold: "process_hygiene_axiom"
  rule: |
    SE uma Instância do Nível 6 encerra alcançando o cão terminal `COMPLETA` com aprovação final
    ENTÃO um Script Automático (Worker) DEVE varrê-la compulsoriamente após um TTL curto-fixado da visão de tela ativa para a Gaveta Arquivada Morta sem a sua destruição (Pois a métrica é eternizada).
  veto_condition:
    trigger: "Fazer os operadores Humanos apertarem 'Deletar' em Cards prontos; ou manter uma lista sem fundo de rolagem de 'COMPLETOS eternos'."
    action: "VETO HIGIÊNICO. Deletar queima a métrica viva; e deixar pendurado destrói a usabilidade. Execute o Arquivamento Automático via Automação de Categoria Worker."
```

## Decision Tree
```javascript
IF (a_process_unit_reaches_its_ultimate_positive_state)
  STEP_1: RECORD final timestamps and emit the Instance Report.
  STEP_2: INITIATE a Countdown T-Minus Time To Live (TTL) [e.g. 7 days].
  STEP_3: WHEN TTL == 0, MOVE physical interface link or database visibility scope to archive status `Status="Archived" & is_Active=False`.
    IF (human_tries_to_manually_delete_the_record_to_clean_the_board)
      -> REJECT. Block hard deletion. The metric data feeds global historical analytics.
NEVER:
  Confundir o alívio que é ver "Listas de Trabalhos Realizados Gigantes que provam meu valor" com a miopia e ineficiência técnica de carregar lixo pesado pra visualizar falhas rápidas diárias em tempo real.
```

## Failure Modes

### Misapplication / Excess: "Limpeza Maníaca Instantânea e Fervilhante (Auto-Arquivo T=0)"
- **Trigger:** Configurar Scripts para auto-arquivarem imediatamente as Tasks/Instâncias no mesmo frame em que o usuário aprova de `Em Validação` para `COMPLETA` no Back-End.
- **Manifestation:** O Human da equipe entra na sala após um colega ou IA finalizar os envios para a cliente para celebrar ou conferir e não vê mais a peça na mesa. Ninguém sabe se enviou de verdade, pois a tarefa literalmente evaporou da visão de "Feito Hoje/Esta Semana" com voracidade ninja. Dúvidas pipocam no Slack 10x mais.
- **Detection:** Funcionários perguntam: "Ei, para onde a Arte P05 foi, nós entregamos hoje de manhã?!"
- **Recovery:** O `TTL` (Time-To-Live) das peças concluídas deve possuir aderência à necessidade sócio-psicólogica de ancoragem e reavaliação leve temporal (*Holdover*) = normalmente, a cada final de ciclo longo (Diário, ou Semanal) expurga as velhas ao Invés da Limpeza estéril síncrona.

### Omission / Failure to Activate: "O Cemitério Fantasma Aberto"
- **Trigger:** Processos de "Não mexe nisso, depois a gente vê se quer recuperar o PDF", rodando solto num ambiente de Kanban super complexo como Monday e Notion Database há quase um ano inteiro com cards completados e parados num mar gigantesco. 
- **Manifestation:** O Gestor de Tráfego entra no Board e tem 50 Instâncias paralisadas aguardando orçamento cruzado. Paralelamente a eles, espremidos ali, há 1.200 de "Pagos". A memória da Aba chora. Os agentes demoram 15x mais pesquisando e injetando RAG Data ao responder os prompts por sobrecarga de vetor imundo não-particionado por Active_Status.
- **Detection:** Ruído Operacional massivo, sensação de estresse subliminar ao abrir a tela central da empresa.
- **Recovery:** Adoção forçada. CronJob Global roda toda sexta, 23:59 varrendo tudo `If State == Completa AND TTL > 7 dias THEN MOVE TO /ARCHIVE/ FOLDER`. Tela limpa, cabeça fria. 
- **Prevention:** Uma "view" limpa sempre ganha por Trivialidade da Manutenção de Fluxo.

---

## Validation

**Paradox Resolved:** The tension between preserving complete metrics (no deletion) and maintaining operational clarity (removing from live view) is resolved through **automatic archiving**: instances move to cold storage (`Status="Archived" & is_Active=False`) rather than being deleted, preserving historical analytics while decluttering the active dashboard.

**Test Case:** When an instance reaches `COMPLETA` state with final approval, the automated worker initiates a TTL countdown (e.g., 7 days). Upon expiration, the instance moves to archive status in deep storage—visible only through historical reports or archive queries, never in the hot operational view. Human operators cannot manually delete; manual hard deletion is blocked, enforcing data governance.

**Validation Criteria:**
- ✓ Archiving must be automated via worker schedule (no manual intervention required)
- ✓ TTL must be configurable per organization context (default 7 days)
- ✓ Archive must preserve all metadata for analytics retroactively
- ✓ Live dashboard query filters must exclude archived instances by default
- ✓ Hard deletion is permanently blocked (immutable audit trail)
