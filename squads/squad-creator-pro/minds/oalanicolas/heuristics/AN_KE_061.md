# AN_KE_061 - Process First Then Codify
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub ee0a7008 — workflow creation para squad-creator-pro]

## Purpose

Counter-intuitive: NÃO criar task/workflow/skill formal ANTES de executar o processo manualmente pelo menos 1x. A frase de Alan combina dois insights: (1) "qualquer squad, não só este" — generalizar padrão detectado, e (2) "vamos primeiro executar isso até pra entender o processo e entao criar uma task pra isso" — vivência antes de formalização. A IA tende a criar abstrações prematuramente: gera YAML perfeito para processo que nunca foi testado. O resultado é automação que não reflete a realidade. Execute primeiro → descubra os edge cases → DEPOIS codifique.

## Configuration

```yaml
AN_KE_061:
  name: "Process First Then Codify"
  zone: "excelencia"
  trigger: "Criando processo, workflow, task, ou skill para algo que nunca foi executado manualmente."

  rule: |
    SE criando processo/workflow/skill novo
    ENTÃO executar MANUALMENTE pelo menos 1x para entender o fluxo real.
    SÓ DEPOIS criar task/workflow formal.
    Abstraçcão prematura = automação que ninguém usa ou que faz a coisa errada.
    BÔNUS: se o processo revelou padrão ("qualquer squad, não só este")
      → GENERALIZAR após validação manual, não antes.

  veto_condition:
    trigger: "Criar task YAML, skill SKILL.md, ou workflow .sh para processo nunca executado manualmente."
    action: "VETO — 'vamos primeiro executar isso até pra entender o processo.' Execute 1x manualmente. Documente surpresas. Depois formalize."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Necessidade de Execução Manual Sequencial"
    resolution: "Execute manualmente PARA DESCOBRIR o padrão real, ANTES de automatizar. A automação vem DEPOIS do entendimento empírico, não antes. Evita ciclo de generalização teórica → implementação errada."

  evidence:
    - "[SOURCE: sessão ee0a7008, sinkra-hub] 'sim, isso precisa ser um padrão para qualquer squad, nao so este, vamos toranr isso uma task orifial sua no sinkra-squad, vamos primeiro executar isso até pra entender o processo e entao criar uma taks pra isso'"
    - "[INSIGHT] A frase combina duas heurísticas: (1) generalizar padrão ('qualquer squad, não só este') + (2) executar antes de codificar ('primeiro executar até pra entender'). A ordem importa: execute → generalize → codify."
```

## Decision Tree

```javascript
IF (creating_new_process_or_workflow)
  CHECK: has_been_executed_manually_at_least_once?

    IF (NO) → BLOCK formalization
      STEP_1: EXECUTE manually at least 1x
      STEP_2: DOCUMENT during execution:
        - What worked as expected
        - What surprised (edge cases não previstos)
        - What failed and required adjustment
        - What is SPECIFIC to this case vs GENERALIZABLE
      STEP_3: THEN codify into task/workflow/skill
        USE: real execution notes as ground truth for the spec
        INCLUDE: edge cases discovered during manual run

    IF (YES) → PROCEED to formalization
      ADDITIONAL CHECK: is this pattern generalizable?
        IF ("qualquer squad, não só este") → generalize AFTER validation
        IF (specific to one domain) → keep scoped

  NEVER: create YAML/SKILL.md from theoretical understanding only
  NEVER: generalize pattern before validating it manually in 1+ case
  ANTI-PATTERN: "perfeito na teoria, inútil na prática" — o YAML bonito que ninguém usa
```

## Failure Modes

### O Workflow Perfeito que Ninguém Usa
- **Trigger:** IA cria validate-skill.sh com 15 checks complexos sem ter executado 1 validação manualmente.
- **Manifestation:** Script roda mas checks não refletem problemas reais. Coverage alta, relevância baixa.
- **Detection:** Script tem 0 runs reais antes de ser commitado. Checks são teóricos.
- **Prevention:** Execute validação manual primeiro. Documente os problemas encontrados. DEPOIS crie o script a partir dos problemas reais.

## Validation

✓ **Paradoxo Identificado:** Exigir execução manual ANTES de codificar conflita com pressão por automação imediata (AN_KE_098). Resolve-se ordenando: empirismo → generalização → codificação.

✓ **Sistema de Tensão:** Registrado em `sys_tension` como tensão deliberada com padrões de automação precoce e otimização prematura.

✓ **Aplicabilidade:** Heurística é generalista ("qualquer squad, não só este") — aplica a processes, workflows, skills, tasks em qualquer domínio.
