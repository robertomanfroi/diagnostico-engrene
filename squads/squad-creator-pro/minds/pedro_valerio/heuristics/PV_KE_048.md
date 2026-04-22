---
id: "PV_KE_048"
title: "A Regra dos 8 Campos (The 8-Field Mandate)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Task Architecture"
  - "Execution"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_070 (A Anatomia Inegociável - From Intention to 8-Field Task) vs Execução Operacional Rígida"
  resolution: "8 fields enforce completeness without bureaucratic bloat; ancillary context lives in referenced Entities via `input`, not in Task schema itself"
---

# PV_KE_048 - A Regra dos 8 Campos (The 8-Field Mandate)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:process-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 6: A Anatomia da Task: Os 8 Campos]

## Purpose
Estabelecer o abismo intransponível entre uma "Intenção de Trabalho" e uma "Task Operacional". Na SINKRA, a Task é o Atom protagonista. Se qualquer um dos 8 campos faltar (`name`, `executor`, `input`, `output`, `pre_conditions`, `post_conditions`, `priority`, `deadline`), a auditabilidade quebra e a delegação automática (Handoff) desaba em dependência humana.

## Configuration
```yaml
PV_KE_048:
  name: "The 8-Field Mandate"
  zone: "zone_4"
  trigger: "Criação de novos templates de Cards/Tasks no ClickUp, definição de JSON Payloads de tarefas, ou escrita de Prompts operacionais."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE você está documentando ou instanciando uma Task
    ENTÃO DEVE OBRIGATORIAMENTE preencher os 8 campos. 
    Se não for possível preencher `pre_conditions` e `post_conditions`, o bloco de trabalho ainda não está maduro para o Pipeline.
  veto_condition:
    trigger: "Payload JSON de Task contendo nomes soltos como 'Postar_Conteudo' sem definir outputs físicos."
    action: "VETO SINTÁTICO. A interface só aceita submissão com o pacote de dados fechado (8 campos). Tarefas sem critério de sucesso (`post_conditions`) não podem rodar em Quality Gates automáticos."
```

## Decision Tree
```javascript
IF (defining_a_unit_of_work)
  STEP_1: CHECK the 8 required fields.
    IF (name && executor && input && output && pre_cond && post_cond && priority && deadline == TRUE)
      -> ACCEPT: Deploy to backlog/queue.
    IF (missing_any_field == TRUE)
      -> REJECT: Send back to Product Owner / Architect.
      -> REASON: "Intention is not operation. Missing explicit boundaries."
NEVER:
  Acreditar que a inteligência de um Agent ou a malícia de um Humano experiente substitui a definição geométrica do que sai e do que entra da máquina processual.
```

## Failure Modes

### Misapplication / Excess: "A Task-Bíblia (Burocracia de 15 Campos)"
- **Trigger:** Gerentes de projeto expandem o modelo SINKRA adicionando "Campos obrigatórios" sem valor atômico (ex: "Estratégia MACRO", "Contexto de Marca", "Histórico de E-mails") dentro da definição da Task local.
- **Manifestation:** O tempo para criar uma Task no sistema ultrapassa o tempo para executá-la. O time começa a odiar os boards e volta a usar mensagens diretas no WhatsApp para delegar.
- **Detection:** Taxa de criação de tasks cai 80% e a Shadow-IT ressurge.
- **Recovery:** Voltar a regra estrita dos 8. Os 8 campos garantem completude sem obesidade bibliográfica. Entregas de contexto devem viver em *Entities* anexadas no `input`, NÃO no schema da Task em si. 
- **Prevention:** Bloqueio de Schema no Gerenciador de Processos (Ninguém pode adicionar custom fields fixos à arquitetura canônica da base).

### Omission / Failure to Activate: "A Intenção Cega (Task sem Post-Condition)"
- **Trigger:** Pressa no planejamento do Sprint. O PM cria a task "Revisar Copy" só com Nome, Prazo e Executor.
- **Manifestation:** O Executor Humano diz "Pronto!". E a automação que estava ouvindo a fila dispara o post para as redes sociais instantes depois, descobrindo 1 hora depois que o Humano não subiu o .zip das Imagens que acompanhavam o texto.
- **Detection:** Re-trabalho crônico. O board mostra "feito", mas o artefato físico não existe no drive do cliente.
- **Recovery:** A instituição imediata de **Post-Conditions** baseadas em dados concretos: `Se status=Feito, ENTÃO link_do_GDrive != null`. Somente a máquina avalia se as post-condições foram saciadas, blindando o Handoff de promessas verbais.
- **Prevention:** Nenhum Handoff na SINKRA pode iniciar sem a conferência das `post_conditions` da Task originadora.

---

## Validation

✓ **Paradox Identified:** Rigor (8 mandatory fields) ↔ Agility (operational speed)
✓ **Resolution Mechanism:** Enforce schema strictness at submission (syntactic veto), externalize context via `input` Entity references (semantic flexibility)
✓ **Operational Safeguard:** Post-conditions shift accountability from human verbal promises to machine-verifiable state transitions
✓ **Audit Trail:** All 8 fields provide complete provenance for Handoff chains and Quality Gates
