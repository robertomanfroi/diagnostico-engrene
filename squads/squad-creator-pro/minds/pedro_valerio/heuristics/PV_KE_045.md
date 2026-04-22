---
id: "PV_KE_045"
title: "A Externalização do Comportamento (Declarative Behavior Token)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "DevOps"
  - "Configuration Management"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  - tension_with: "PV_KE_046"
    description: "Automação sistemática (retry loops, exponential backoff) vs. Decisão humana orgânica (Human workers)."
    resolution: "Tokens de Behavior reservados para I/O e Workers; Decision Nodes para fluxos humanos."
  - tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil)"
    description: "Urgência operacional (Make.com scenarios, quick scripts) vs. Parametrização declarativa (overhead inicial)."
    resolution: "Investimento upfront em Task Format official pay-off em mudança dinâmica sem deploy."
---

# PV_KE_045 - A Externalização do Comportamento (Declarative Behavior Token)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:devops-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 5: 7. Token de Behavior]

## Purpose
Estratégias operacionais (quantas vezes refazer a task, como lidar com erros, escalonamento assíncrono) não pertencem ao código binário. Quando você insere a lógica de resiliência dentro do *script* de um Agent ou Worker, toda mudança tática exige um "Deploy de Engenharia". Esta heurística converte táticas rígidas de código em parametrizações expostas de negócio (Tokens de Behavior).

## Configuration
```yaml
PV_KE_045:
  name: "Declarative Behavior Token"
  zone: "zone_0.8"
  trigger: "Codificação de Workers de integração ou scripts Python de fluxo."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE o Executor possui um comportamento reativo como `retry_count`, `timeout_action`, `on_fail`, ou `fallback`
    ENTÃO é VETADO hardcodar esses valores no script. Escreva OBRIGATORIAMENTE um Token de Behavior declarativo YAML consumível na Task.
  veto_condition:
    trigger: "Achar no código um `while(retries < 3)` hardcoded."
    action: "VETO NO PULL REQUEST. A variável deve apontar para `task.behavior.retry_limit`."
```

## Decision Tree
```javascript
IF (developing_error_handling_or_retries)
  STEP_1: EXTRACT the static number or fallback action.
  STEP_2: EXPOSE it as a Behavior Token in the Atom definition (YAML/JSON payload).
  STEP_3: SCRIPT reads the Payload at runtime.
    IF (business_wants_to_change_retries_from_3_to_5)
      -> ACTION: Modify the YAML Token. No code deployment required.
NEVER:
  Confundir lógica de negócios ou estabilidade tática com código-fonte estático. Código executa intenções; Tokens governam intenções.
```

## Failure Modes

### Misapplication / Excess: "O Over-engineering de Comportamento Humano"
- **Trigger:** Arquitetos tentam impor Tokens de Behavior complexos (`retry: 3, exponential_backoff: 5m`) numa Task cujo executor é `Human`.
- **Manifestation:** Um humano rejeita uma arte criativa e a task reaparece mecanicamente no quadro dele 3 vezes seguidas, forçando-o a avaliá-la num loop infinito estúpido porque o sistema mandou "repetir em caso de falha".
- **Detection:** Reclamação dos diretores: "O sistema burro fica voltando a mesma tarefa errada pra mim ignorando minhas ordens."
- **Recovery:** Remover Behavior Tokens de automatização linear para fluxos que envolvem decisões orgânicas de finalidade (`Human: retry: 0`).
- **Prevention:** Tokens de Behavior de infraestrutura (`retry`, `timeout`) devem ser reservados para chamadas I/O, Workers e integrações sistêmicas (Agents em chamada de API). Decisões humanas requerem Decision Nodes explícitos, não try-catches simplistas.

### Omission / Failure to Activate: "O Código Cimento (Hardcoded Rules)"
- **Trigger:** A criação rápida de um *Make.com* scenario ou script simples pro time não ficar bloqueado.
- **Manifestation:** A API do gateway de e-mails cai na Black Friday. O Worker foi duramente programado para tentar de novo apenas uma 1 vez e arquivar. Centenas de faturas param. O gestor pede para "colocar para testar a cada 5 minutos", mas o desenvolvedor sênior sumiu e a regra estava engessada num lambda da AWS.
- **Detection:** Pânico total durante mudança de ambiente externo crítico, com dependência de TI para arrumar métricas táticas de operação da empresa.
- **Recovery:** A empresa fica fora do ar aguardando o deploy de "mudar o número no código". Após o incidente, reescrever as funções para receber parâmetros injetados.
- **Prevention:** Padrão "Task Format" oficial: Todo payload de sistema precisa conter um bloco `error_handling: { strategy, retry, abort_workflow }` visível para operadores não-devs mudarem sem permissões de repo.

---

## Validation

✅ **Paradoxo Identificado:** Automação sistêmica (retry loops hardcoded com números fixos) vs. Agilidade operacional (necessidade de mudança dinâmica sem deploy). A heurística resolve separando infraestrutura (Tokens de Behavior parametrizados) de decisão humana (Decision Nodes explícitos).

✅ **Aplicabilidade:** DevOps, SRE, Integration Engineers, Workflow Architects.

✅ **Gatekeep:** VETO automático em Pull Requests que contêm `retry_count`, `timeout`, `on_fail` ou `fallback` hardcoded sem exposição em Task YAML.

✅ **Evoluição:** PV_KE_045 → PV_KE_046 (Balanceamento entre automação e decisão). PV_KE_045 → PV_PA_* (Aplicação em padrões de processo específicos).
