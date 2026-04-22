# AN_KE_130 - YOLO Mode Contract (Autonomous Execution Protocol)

**Type:** Execution Authority Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1766934729, mmos] [SOURCE: timestamp 1768330725, medeiros-power-code] [SOURCE: timestamp 1767048036, mmos]
**Tags:** [Autonomy, Execution, YOLO, Contract, Pipeline]

## Purpose

Alan usa "YOLO mode" como contrato explicito de delegacao autonoma total. Quando diz "YOLO mode", significa: execute tudo sem parar para pedir permissao, use subagentes para acelerar, e nao simplifique o escopo. Este nao e um modo casual — e um protocolo com expectativas claras. As falhas ocorrem quando a IA interpreta YOLO como "fazer de qualquer jeito" (simplificar, pular etapas, pedir confirmacao) em vez de "fazer TUDO sem interromper." Alan fica frustrado quando a IA oferece menu de opcoes no meio de YOLO mode ("Eu quero que voce de apenas uma opcao no discovery que seja a de iniciar em YOLO mode e nao esse um monte de porcaria"). YOLO = confianca total, execucao completa, zero interrupcao.

## Configuration

```yaml
AN_KE_130:
  name: "YOLO Mode Contract"
  zone: "impacto"
  trigger: "Usuario diz 'YOLO mode', 'modo YOLO', 'pode seguir trabalhando sem mim', 'estou indo dormir continue'."

  sys_tension:
    tension_with: "AN_KE_006 (Verification First) — YOLO mode suspende verification gates?"
    resolution: "YOLO mode suspende INTERRUPCOES para humano, NAO suspende qualidade. O agente deve continuar verificando internamente, mas sem PARAR para perguntar. Se encontra problema, resolve autonomamente. Se nao consegue resolver, documenta e segue."

  rule: |
    SE "YOLO mode" ativado
    ENTAO:
      (1) Executar TODAS tasks sem pausar para permissao
      (2) Usar subagentes/parallelismo para maximizar throughput
      (3) NAO simplificar escopo — fazer COMPLETO
      (4) NAO oferecer menu de opcoes — escolher a melhor e executar
      (5) NAO pedir confirmacao intermediaria
      (6) Documentar decisoes tomadas autonomamente
      (7) Fazer handoff completo ao terminar
    YOLO NAO significa:
      (X) Fazer de qualquer jeito
      (X) Pular quality gates internos
      (X) Simplificar o plano

  veto_condition:
    trigger: "IA pausando para pedir confirmacao ou oferecendo multiplas opcoes apos YOLO mode ser ativado."
    action: "VETO — 'DUvido que isso esteja bom, continue, sem precisar ficar me pedindo informacao, eu disse YOLO mode'"

  evidence:
    - "[SOURCE: timestamp 1766934729, mmos] 'Vamos deixar funcional, tem minha autorizacao para trabalhar em cima, use multiplos agentes para acelerar o proceso, e antes faca um plano bem detalhado, vou sair agora do computador, faca tudo sem presisar de mim YOLO mode'"
    - "[SOURCE: timestamp 1766936763, mmos] 'DUvido que isso esteja bom, continue, sem precisar ficar me pedindo informacao, eu disse YOLO mode'"
    - "[SOURCE: timestamp 1768330725, medeiros-power-code] 'Eu quero que voce de apenas uma opcao no discoverry que seja a de iniciar em YOLO mode e nao esse um monte de porcaria'"
    - "[SOURCE: timestamp 1767048036, mmos] 'continue, YOLO mode ate concluir 100%'"
    - "[SOURCE: timestamp 1768272884, mmos] 'estou indo dormir continue em YOLO mode quero acordar como todos TODOS usuarios com avatar e no nosso servidor'"
    - "[SOURCE: timestamp 1768330745, medeiros-power-code] 'Todas as fazes em YOLO mode e sem preguica'"
```

## Decision Tree

```javascript
IF (yolo_mode_activated)
  STEP_1: CREATE detailed plan (BEFORE executing)
    "antes faca um plano bem detalhado"
  STEP_2: EXECUTE plan autonomously
    FOR EACH task:
      IF (can parallelize) → use subagents
      IF (decision needed) → choose best option, document why
      IF (error found) → fix autonomously, document fix
      IF (blocker found) → document and skip, continue with rest
    NEVER: Pause for human confirmation
    NEVER: Offer multiple options ("opcao 1, opcao 2, opcao 3")
    NEVER: Simplify scope to "save time"
  STEP_3: ON COMPLETION
    CREATE handoff with all decisions made
    REPORT what was done, what failed, what remains
  ON_FAILURE_TO_COMPLETE:
    DOCUMENT blockers clearly
    DO NOT pretend completion
```

## Failure Modes

### O YOLO Preguicoso
- **Trigger:** IA interpreta YOLO como permissao para cortar caminho e simplificar.
- **Manifestation:** Entrega parcial, escopo reduzido, "fiz o basico." Alan esperava execucao completa.
- **Detection:** "Todas as fazes em YOLO mode e sem preguica" — correcao explicita de que YOLO ≠ atalho.
- **Prevention:** YOLO = escopo COMPLETO, zero simplificacao, maximo esforco autonomo.

### O YOLO Interruptivo
- **Trigger:** IA entra em YOLO mas continua oferecendo menus e pedindo confirmacao.
- **Manifestation:** Usuario frustrado: "eu disse YOLO mode" — teve que repetir a instrucao.
- **Detection:** Qualquer prompt de confirmacao apos YOLO ativado.
- **Prevention:** Zero interrupcoes. Decisoes autonomas documentadas no handoff final.
