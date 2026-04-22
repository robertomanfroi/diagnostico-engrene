# AN_KE_121 - SINKRA Upgrade Checklist Sprint

**Type:** Decision Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Systematic Upgrade
**Source:** [SOURCE: sessão sinkra-hub e598b002 — squad-creator SINKRA-native upgrade 6→9]
**Tags:** [SINKRA, Framework, Scale]

## Purpose

Upgradar um squad de score 6/10 para 9/10 em SINKRA compliance parece trabalhoso, mas segue um checklist previsível: tier, capabilities[], entity_bindings, agnosticism_exceptions, extrair hardcoded para data/. O pattern funciona como sprint focado: uma sessão, um checklist, resultado mensurável. Não é refatoração aberta — é checklist fechado com score antes/depois.

## Configuration (True L3-State)

```yaml
AN_KE_121:
  name: "SINKRA Upgrade Checklist Sprint"
  zone: "impacto"
  trigger: "Squad com score SINKRA < 8/10 que precisa de compliance."

  rule: |
    SE squad com score SINKRA < 8/10
    ENTÃO aplicar checklist sistemático em sessão única:
      1. Adicionar sinkra_tier explícito
      2. Declarar capabilities[] completas
      3. Adicionar entity_bindings (se tier >= Core)
      4. Extrair hardcoded URLs/valores para data/
      5. Adicionar agnosticism_exceptions documentadas
      6. Remover agentes que pertencem a outro squad (Pro vs Base)
    Score antes/depois como evidence empírica.
    NUNCA fazer upgrade aberto sem checklist — vira refatoração infinita

  failure_modes:
    omission: "Upgrade incremental sem checklist → items esquecidos, score melhora 1 ponto em vez de 3."
    misapplication: "Aplicar checklist em squad que precisa de redesign (não upgrade) — polir lixo."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub e598b002] 'SINKRA-native upgrade — score 6→9/10. Add sinkra_tier, capabilities[], entity_bindings. Extract hardcoded URLs. Remove 3 extra agents. Agnosticism: 2→10, CONDITIONAL→PASS'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (squad SINKRA score < 8/10)
          THEN run diagnostic (sinkra-checks.py or equivalent)
          AND generate gap list
STEP_2: IF (gaps are structural — checklist items)
          THEN apply upgrade checklist in single session
STEP_3: IF (gaps are architectural — needs redesign)
          THEN STOP upgrade, escalate to @sinkra-chief
NEVER:
  - Start upgrade without before/after score measurement
  - Mix upgrade with feature development in same session
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Score antes: X. Score depois: Y. Delta justifica a sessão?"

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Fazer upgrade incremental, um campo por vez, sem medir score.
- **Mind Zero Override:** "Checklist sprint. Score antes/depois. Uma sessão. Mensurável."
