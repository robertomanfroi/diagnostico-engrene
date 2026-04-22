---
id: "PV_KE_062"
title: "O Ponto de Origem da Mensuração (Without Instance, Timeline Doesn't Exist)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Tracking"
  - "System Reliability"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_106 (Subagents Over Flattened Tasks) vs Instanciação Linear Obrigatória"
  resolution: "Formality required for normal operations; suspended only during P0 incidents with mandatory post-mortem retroactive documentation. C-Level has sovereign override authority, but must trigger recovery procedures afterward."
---

# PV_KE_062 - O Ponto de Origem da Mensuração (Without Instance, Timeline Doesn't Exist)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:process-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 10: A Ilusão da Execução Isolada]

## Purpose
Explicar que um evento de trabalho nunca começou na métrica governamental a menos que uma **Identidade Explícita com ID e Timestamp de Origem** seja gerada e assinada. Empurrar cards numa parede eletrônica (Kanban informal) não configura a existência dimensional linear de tempo porque o evento não foi instanciado (Status = CRIADA) pelo sistema raiz. 

## Configuration
```yaml
PV_KE_062:
  name: "Genesis of Trackable Work"
  zone: "zone_4"
  trigger: "Quando equipes preferem iniciar ações antes de registrar a solicitação nos motores formais (banco/jira/squad)."
  evidence_threshold: "cybernetic_law"
  rule: |
    SE você deseja reclamar sobre atraso, cobrar SLA ou reportar Gargalo
    ENTÃO uma Instance de Template contendo o ID exclusivo de Execução e `criada_em` DEVE ser instanciada oficialmente.
    Não se controla e não se computa sobre entidades soltas em tempo fantasma.
  veto_condition:
    trigger: "Fazer requests gigantes pelo Whats/Slack e reclamar pro Head de Automação que não andou porque 'Eu pedi na sexta'."
    action: "VETO PROCEDURAL. 'Pedi na sexta' é barulho de corredor. Instanciou a Pipe BBB-07 na Worker Base? Não? O evento é nulo para nós."
```

## Decision Tree
```javascript
IF (auditing_a_workflow_complaint_of_being_late_or_blocked)
  STEP_1: QUERY the system logger for the specific Instance ID.
    IF (ID_Not_Found == TRUE && Request_was_made_randomly_in_a_meeting)
      -> REJECT. "The stopwatch hasn't started. The machine is not liable."
    IF (Instance_Exists && Current_Time > SLA_Parameter_Injected)
      -> ACCEPT: "The machine accepts liability. SLA violated since T[Criada]".
NEVER:
  Substituir a instância explícita tecnológica inicial (O Big Bang da Tarefa) por ordens vocais de passadiço.
```

## Failure Modes

### Misapplication / Excess: "A Tirania do ID Rígido em Micro-Operações de Sobrevivência"
- **Trigger:** Num momento de crise total de incêndio ou vazamento no ambiente LIVE, as mentes SINKRA forçarem a espera para criar instâncias formais, IDs, e preenchimento numérico em payload limpo enquanto os servidores da companhia explodem online, exigindo conserto manual que levariam dez segundos soltos mas atrasando a sangria.
- **Manifestation:** Perda severa de dinheiro e infraestrutura pela burocracia rígida operante durante o "Death Valley".
- **Detection:** Falas tipo "Eu ia rodar o script de desabar a nuvem de contingência só que o WorkerTriage ainda tava logando a abertura do Pipe... e pegamos fogo completo".
- **Recovery:** Break-Glass Protocol. Procedimentos de altíssima emergência operam por cima ou sem instânciação linear durante a fase aguda, desde que o Post-Mortem reconstrua retrospectivamente ou seja feito um Ticket retroativo "Fix de Emergência" cobrindo o fuso gasto posterior.
- **Prevention:** Nenhum design arquitetural rígido anula a autoridade soberana e destrutiva do C-Level para bypasses físicos temporários em P0 Critical Incidents.

### Omission / Failure to Activate: "O Board de Adesivos (The Informal Operation)"
- **Trigger:** "Gente, não precisa preencher muito, esse cliente aqui é só criar no notion os tickets de Design e vamo girando lá pro cara aprovar."
- **Manifestation:** No dia do prestação de contas, o head de Operações é inquirido sobre qual foi o lucro marginal sobre os 400 tickets girados pra ele. Como nada do Notion possuia T[start] e T[end] em ID de Pipeline rastreado... o time apenas sente e "deduz" que lucraram algo. Estão gerindo um Bar do bairro na década de 80 apostando no caderno fiado. Sem um ciclo formal documentado de Lifecycle (CRIADA -> COMPLETA), as campanhas se desfazem como pó e os lucros vazam pro vazio estatístico.
- **Detection:** Muito trabalho mental e relacional; pouquíssimos registros duros do volume fático.
- **Recovery:** Reinstituir o bloqueio sagrado de execução. Nada passa do Nível de Ideia pro Nível de Máquina sem a emissão de um RG único provindo do Banco de Dados gerador das Instâncias.
- **Prevention:** Uma Task que não pertence organicamente dentro do útero (Array) de uma Instance ativa em Banco, será destruída sem aviso prévio. Se não tem raiz, é lixo cósmico.

## Validation

✅ **Paradox Identified:** The heuristic enforces strict instancing requirements (formal ID + timestamp) for operational accountability, yet acknowledges that P0 critical incidents require bypass of this very instancing discipline to prevent catastrophic loss. This creates systemic tension between governance rigor and operational survival.

✅ **Resolution Applied:** Break-Glass Protocol permits C-Level override during P0 scenarios, BUT with mandatory post-mortem reconstruction of timelines and retroactive ticketing. The paradox is resolved by **context-dependent rigor**: normal state = formality required; emergency state = formality suspended with recovery obligation.

✅ **Application Boundary:** Heuristic applies to steady-state operations. Emergency protocols operate in a separate authority domain (P0 Incident Response) with explicit escalation conditions and post-incident documentation requirements.
