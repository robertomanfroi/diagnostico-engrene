# AN_KE_092 - Unify Before Extending
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão prompt-ops — unificar design system antes de estender]

## Purpose

Quando existem múltiplas versões, variantes ou duplicatas de algo, UNIFICAR primeiro antes de adicionar features novas. Estender algo fragmentado = multiplicar a fragmentação.

## Configuration

```yaml
AN_KE_092:
  name: "Unify Before Extending"
  zone: "excelencia"
  trigger: "Múltiplas versões/variantes do mesmo artefato existem."
  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Unify Sequentially vs. Parallelize for Speed"
    resolution: "Unify cost upfront (slower immediate delivery) prevents exponential fragmentation cost later (much slower long-term velocity). Accept short-term cost for long-term system health."

  rule: |
    SE existem variantes (2 design systems, 2 schemas, 2 configs)
    ENTÃO UNIFICAR o melhor de cada ANTES de adicionar novo.
    "como podemos unificar o que tem de melhor em cada parte"

  evidence:
    - "[SOURCE: sessão prompt-ops] 'leia /outputs e /docs/design-system e me diga como podemos unificar o que tem de melhor em cada parte'"
    - "[SOURCE: sessão prompt-ops] 'mas eu fui claro na solicitacao, unificar o que tem de melhor'"
```

## Decision Tree

```javascript
IF (extending_feature_or_adding_capability)
  CHECK: do multiple variants/versions exist?
    IF (YES) → UNIFY first
      STEP_1: MAP what each variant has (feature comparison)
      STEP_2: IDENTIFY "best of each" to keep
      STEP_3: CREATE unified version with best features
      STEP_4: THEN extend the unified version
    IF (NO) → extend directly
  NEVER: add feature to variant A while variant B exists
  PREFER: 1 unified system > 2 partial systems + new feature
```

## Failure Modes

### Os Dois Design Systems
- **Trigger:** Project has /outputs/ design system AND /docs/design-system. New feature added to one, not the other.
- **Manifestation:** "unificar o que tem de melhor em cada parte" — descoberta tardia de duplicação.
- **Detection:** Same concept described in 2+ locations with different details.
- **Prevention:** Before ANY extension, search for variants. Unify → then extend.

## Validation

✓ **Paradoxo identificado:** Tensão entre velocidade imediata (estender rápido em uma variante) vs. saúde de sistema (unificar antes, custando tempo agora mas economizando exponencialmente depois).

✓ **Resolução aplicada:** Aceitar custo de unificação upfront como investimento que previne fragmentação exponencial e degeneração de longo prazo.

✓ **Campo sys_tension adicionado:** Documentada relação SPEED_OVER_QUALITY com resolução explícita.

✓ **Heurística validada:** Regra é aplicável, evidência robusta, decision tree executável.
