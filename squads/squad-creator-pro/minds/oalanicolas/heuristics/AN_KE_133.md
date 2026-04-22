# AN_KE_133 - Prohibition as System Rule (NUNCA/JAMAIS → CLAUDE.md)

**Type:** Governance Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1766936643, mmos] [SOURCE: timestamp 1768929794, mmos] [SOURCE: timestamp 1769153848, mmos]
**Tags:** [Governance, Rules, Prohibition, CLAUDE.md, Anti-Pattern]

## Purpose

Quando Alan descobre um erro que causa frustacao intensa, ele nao apenas corrige — exige que a proibicao seja CODIFICADA no sistema (CLAUDE.md, regras do agente, config) para que NUNCA mais aconteca. Isso nao e apenas irritacao momentanea; e um pattern de governanca por proibicao explicita. A intensidade linguistica ("NUNCA, JAMAIS", "escreva isso ate na sua porra da sua bunda se for necessario", "atualize o claude.md e o caralho") sinaliza que a regra deve ser permanente e inviolavel. Exemplos concretos: nunca clonar tabelas como backup no Supabase (AN_KE_068 nasceu assim), nunca usar colunas em portugues no DB, nunca inserir metadados de pipeline no output final, nunca usar emojis em interfaces de produto. O pattern e: frustacao → proibicao verbal → codificacao em CLAUDE.md → enforcement permanente.

## Configuration

```yaml
AN_KE_133:
  name: "Prohibition as System Rule"
  zone: "impacto"
  trigger: "Erro que gera frustacao intensa e repeticao ('NUNCA', 'JAMAIS', 'PROIBIDO'). Especialmente quando o mesmo erro aparece pela segunda vez."

  sys_tension:
    tension_with: "AN_KE_008 (Pattern Recognition 2x Rule) — formalizar apos 2 ocorrencias"
    resolution: "AN_KE_008 e o threshold generico (2 ocorrencias → regra). AN_KE_133 e o MECANISMO: erro grave → proibicao EXPLICITA codificada no sistema. AN_KE_008 detecta o pattern, AN_KE_133 executa a codificacao."

  rule: |
    SE Alan diz "NUNCA", "JAMAIS", "PROIBIDO" com emocao intensa
    ENTAO:
      (1) ENTENDER a proibicao (o que exatamente e proibido?)
      (2) CODIFICAR no local correto:
        - Regra generica → CLAUDE.md
        - Regra de agente → config do agente/squad
        - Regra de banco → constraint no schema
        - Regra de CI → validador automatico
      (3) CONFIRMAR que a proibicao esta enforced automaticamente
    NAO BASTA "entender e evitar" — deve estar ESCRITO e ENFORCED
    A proibicao sobrevive ao reset de sessao, de agente, de projeto

  veto_condition:
    trigger: "Erro proibido acontece pela segunda vez apesar de ja ter sido comunicado."
    action: "VETO CRITICO — 'Nao acredito em voce, me prove que nunca mais vai acontecer'"

  evidence:
    - "[SOURCE: timestamp 1766936643, mmos] 'nunca crie backups no supabase, duplicando a tabela, baixe ela mas nUNCA jamais crie bckups duplicando a tabela no supabase, escreva isso ate na sua porra da sua bunda se for necessario, atualize o claude.md e o caralho, mas nao faca isso de novo'"
    - "[SOURCE: timestamp 1768929794, mmos] 'NUNCA, JAMAIS ADICIONE NO FINAL ESSA PORRA: DE ONDE TA VINDO ESSA MERDA??'"
    - "[SOURCE: timestamp 1769153848, mmos] 'como ousa indicar nome de colunas em portugues? esta nas instrucoes que isso e proibido'"
    - "[SOURCE: timestamp 1768519592, mmos] 'nao use emojis, isso e proibido'"
    - "[SOURCE: timestamp 1761675824, mente_lendaria] 'Nao acredito em voce, me prove que nunca mais vai acontecer'"
    - "[SOURCE: timestamp 1769041285, mmos] 'como posso tonar essa frase ou filosofia um mantra no claude.md? nunca, jamaiss escolha o caminho do retrabalho, fazemos o trabalho dificil hoje, sem preguica'"
```

## Decision Tree

```javascript
IF (user_expresses_prohibition with intensity >= HIGH)
  STEP_1: EXTRACT the exact prohibition
    WHAT is forbidden? (backup by cloning, PT-BR columns, emojis, metadata in output)
  STEP_2: IDENTIFY enforcement location
    IF (affects all agents) → CLAUDE.md
    IF (affects specific agent) → agent config / squad config
    IF (affects database) → schema constraint / check constraint
    IF (affects CI) → validation script
  STEP_3: CODIFY prohibition
    ADD explicit rule with "NUNCA" / "PROIBIDO" language
    INCLUDE the reason (WHY it's forbidden)
    INCLUDE the detection (HOW to catch violation)
  STEP_4: VERIFY enforcement
    CAN the system catch this violation automatically?
    IF (yes) → add automated check
    IF (no) → add to checklist/gate
  NEVER: Just "remember" the prohibition without codifying
  NEVER: Assume next session will remember verbal prohibition
```

## Failure Modes

### A Proibicao Amnésica
- **Trigger:** Erro proibido verbalmente mas nunca codificado em CLAUDE.md ou config.
- **Manifestation:** Erro repete na proxima sessao. "NUNCA" nao sobreviveu ao reset de contexto. Usuario furioso.
- **Detection:** "esta nas instrucoes que isso e proibido" — mas nao estava, ou estava mas agente nao leu.
- **Prevention:** Toda proibicao verbal com intensidade alta → imediata codificacao em config persistente.

### A Proibicao Sem Enforcement
- **Trigger:** Regra escrita no CLAUDE.md mas sem mecanismo automatico de detecao.
- **Manifestation:** Agente viola regra que esta documentada mas nao enforced. "Tem nas regras mas ninguem verifica."
- **Detection:** Violacao encontrada manualmente pelo humano.
- **Prevention:** Toda proibicao codificada deve ter pelo menos um checkpoint: CI gate, pre-push hook, ou validation script.
