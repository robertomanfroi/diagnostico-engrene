# PV_KE_101 - Automation Manual Parity (The Step-by-Step Transparency)
**Zone:** 🛡️ Mapeamento L1 | **Agent:** @pedro-valerio
**Source:** [SOURCE: sessão de chat, 30/03/2026 — "tudo que existe como automacao tem que existir uma task manual"]

## Purpose

A automação não pode ser uma "caixa preta" inquebrável. Quando um workflow de ponta a ponta falha misteriosamente no meio da madrugada, a ausência de controle manual destrói a operação. Pedro Valério estipula a "Paridade Manual": **toda e qualquer automação construída deve possuir obrigatoriamente uma Task individual correlata que pode ser acionada manualmente**. Além disso, workflows não podem ser monólitos monolíticos; eles devem ser uma corrente de Tasks isoladas, onde o output de uma possa ser inspecionado, validado e então utilizado como input para a próxima. O sistema é operável "by wire" (automático) ou "override" (humano).

## Configuration

```yaml
PV_KE_101:
  name: "Automation Manual Parity (Step-by-Step Transparency)"
  zone: "processos/mapeamento"
  trigger: "Desenhando ou programando uma automação end-to-end, workflows n8n longos ou pipelines agenticas (Epic)."

  rule: |
    SE você criar um `workflow` ou script de Automação
    ENTÃO OBRIGATORIAMENTE garanta que suas entranhas são Tasks (funções/scripts/etapas) separadas.
    Cada passo DEVE poder ser acionado e testado MANUALMENTE com inputs forçados.
    NUNCA crie uma Blackbox onde a Etapa A funde magicamente na B sem a chance de validação humana e handoff do Output -> Input.

  veto_condition:
    trigger: "Agente projeta um arquivo único Python de 500 linhas de automação contínua que baixa os leads, filtra os lixos, manda e-mail e deleta do banco, sem separar em etapas isoladas."
    action: "VETO — 'tudo que existe como automação tem que exister uma task que eu chamo manualmente também... E todo workflow tem que ter tasks separadas com output validado'."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents) vs Opressão Monolítica (Blackbox Flow)"
    resolution: "Enquanto AN_KE_073 acelera a execução via paralelismo, PV_KE_101 garante que a arquitetura dessas execuções seja DECOMPOSTA e TESTÁVEL por um humano (Override). Autonomia (Alan) opera unicamente suportada pela Rastreabilidade Categórica (Pedro). O workflow deve ser como blocos de LEGO."

  evidence:
    - "[SOURCE: chat 30/03/2026] 'sim, uma regra que eu uso aqui é. tudo que existe como automação tem que exister uma task que eu chamo manualmente também'"
    - "[SOURCE: chat 30/03/2026] 'E todo workflow tem que ter tasks separadas possíveis de serem executas manualmente com output validado para virar input de um próxima task'"
```

## Decision Tree

```javascript
IF (building_and_to_end_automation_or_workflow)
  STEP_1: MAP the desired monolith as a sequence of atomic TASKS.
    - [Task 1] Extract leads
    - [Task 2] Clean DB
    - [Task 3] Dispatch Welcome Trigger
  STEP_2: EXPOSE each TASK individually via CLI or UI trigger.
  STEP_3: IMPLEMENT the workflow purely as an ORCHESTRATOR that pipes Task 1 Ouptut -> Task 2 Input.
  STEP_4: CHECK: Can a human run Task 2 bypassing Task 1? If YES -> Approved.
```

## Failure Modes

### The Blackbox Hostage
- **Trigger:** A API do ClickUp muda e a Etapa 3 "Dispatch Welcome" quebra no Workflow AIOX fechado.
- **Manifestation:** Como a automação era uma montanha de código fundida, a equipe de marketing não consegue rodar o "Dispatch Welcome" manualmente subindo o CSV de hoje. A operação para 100%. Tudo ou Nada.
- **Prevention:** Paridade de acionamento manual para cada peça da máquina.

## Validation & Cross-Mind Divergence

**Phase:** Architecture Design & Testing
**Status:** REQUIRED (L4 Compliant)

This establishes the baseline difference between *Scripting* and *System Generation*. Scripts are sequential chains of commands; Systems are ecosystems of components. Pedro dictates that unobservable, un-callable mid-step tasks violate predictability. If it can run on CRON, it MUST run via User CLI with direct arguments.
