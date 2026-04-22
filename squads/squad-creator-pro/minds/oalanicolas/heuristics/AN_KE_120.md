# AN_KE_120 - Auto-Mode Detection (State-Driven Greenfield/Brownfield)

**Type:** Architecture Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Pattern:** State-Driven Mode
**Source:** [SOURCE: sessão sinkra-hub 4c677aed + b520dddb — domain-decoder runner]
**Tags:** [Agnostic, Automation, Pipeline, SINKRA]

## Purpose

Pipelines CLI que pedem "greenfield ou brownfield?" ao user criam um problema: o user frequentemente escolhe errado (greenfield com state existente = perde trabalho; brownfield sem state = erro). A solução confirmada em 3 pipelines independentes: modo default = "auto". Auto detecta: state existe → brownfield (resume), state não existe → greenfield. Override explícito permitido, mas com ação drástica documentada (greenfield explícito com state = WIPE previous run).

## Configuration (True L3-State)

```yaml
AN_KE_120:
  name: "Auto-Mode Detection (State-Driven Greenfield/Brownfield)"
  zone: "excelencia"
  trigger: "CLI pipeline com modos greenfield/brownfield e state persistido entre runs."

  sys_tension:
    tension_with: "AN_KE_085 (Greenfield Over Spaghetti Refactor)"
    resolution: "AN_KE_085 é sobre DECISÃO HUMANA de descartar código sujo. AN_KE_120 é sobre AUTOMAÇÃO do pipeline decidir modo baseado em state. São complementares: humano decide estratégia, pipeline decide tática."

  rule: |
    SE CLI pipeline tem modos greenfield/brownfield
    ENTÃO default mode = "auto":
      - State exists → brownfield (resume from last checkpoint)
      - No state → greenfield (fresh start)
    E greenfield explícito com state existente → WIPE (state, logs, outputs) antes de começar
    NUNCA bloquear com erro quando state existe e mode é greenfield — ou wipe ou switch

  failure_modes:
    omission: "User escolhe greenfield com state, pipeline bloqueia com erro confuso. User escolhe brownfield sem state, pipeline crasheia."
    misapplication: "Auto-mode em pipeline onde state é ambíguo (múltiplas versões coexistindo) pode resumir run errado."

  evidence_threshold: "[SYNTHESIZED] — Confirmado em 3 pipelines independentes"
  evidence:
    - "[SOURCE: sessão sinkra-hub 4c677aed] 'Default mode is now auto: State exists → brownfield, No state → greenfield'"
    - "[SOURCE: sessão sinkra-hub b520dddb] 'Instead of blocking with error when greenfield finds existing state, automatically switch to brownfield'"
    - "[SOURCE: sinkra-map.sh] 'RUN_ID + latest symlink pattern — mesmo conceito'"
    - "[SOURCE: mmos.sh] 'Resume automático de última fase completa'"
    - "[SOURCE: sessão 8b2b58da, decoder.sh] 'Versioned runs: outputs/decoded/{slug}/{version}/ com latest symlink. Auto-detect pega latest → brownfield. Nova versão → greenfield. Mesma versão → resume. Legacy flat state migrado automaticamente para layout versionado.'"
    - "[SOURCE: sessão opus+mmos run] '4ª confirmação: mmos 4.1.0 e squad_creator 4.0.0 ambos rodaram com auto-detect brownfield. Zero intervenção do user.'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (mode == "auto" — default)
          THEN check state file existence
          IF (state exists AND has completed phases) → brownfield (resume)
          IF (no state) → greenfield (fresh)
STEP_2: IF (mode == "greenfield" AND state exists)
          THEN WIPE: remove state, logs, phase outputs
          AND log warning: "Wiping previous run data"
STEP_3: IF (mode == "brownfield" AND no state)
          THEN FAIL with clear error: "No state to resume from"
NEVER:
  - Block with cryptic error when auto-resolution is possible
  - Silently ignore existing state in greenfield mode
```

## Confidence Requirements & Reversibility

- **High-Commitment (One-Way Door):** Greenfield WIPE deletes previous run data permanently.
- **Tactical (Two-Way Door):** Auto-mode detection — can always override with explicit flag.

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "O que acontece se o user roda sem flags? O pipeline faz a coisa certa automaticamente?"

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Pedir confirmação do user para cada decisão de modo.
- **Mind Zero Override:** "Auto-detect > perguntar. 3 pipelines confirmam: sinkra-map, mmos, decoder."
