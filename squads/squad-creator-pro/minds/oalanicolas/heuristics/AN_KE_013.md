# AN_KE_013 - Regra dos 3+ Consumidores

**Type:** Decision Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Abstraction Threshold
**Source:** [SOURCE: Epic 71 — scoring engine validate-squad NÃO extraído (1 consumidor, 7 guardrails específicos)]

---

**sys_tension:**
  - tension_with: "AN_KE_007 (REUSE > CREATE) vs Pragmatic Extraction Threshold"
  - resolution: "Require 3+ independent consumers before extraction; domain-specific logic stays inline"

## Purpose

Só extrair para shared lib quando 3+ scripts usam o mesmo pattern. Com 2 é coincidência. Com 3 é padrão.

## Configuration

```yaml
AN_KE_013:
  name: "Regra dos 3+ Consumidores"
  zone: "excelencia"
  trigger: "Tentação de extrair código para shared lib"

  rule: |
    SE pattern aparece em 1-2 scripts → MANTER inline
    SE pattern aparece em 3+ scripts → EXTRAIR para shared lib
    NUNCA extrair lógica domain-specific (scoring com 7 guardrails de 1 script)

  anti_pattern: "Abstrair prematuramente algo que só 1 script usa"

  evidence:
    - "security scan: validate-skill + validate-squad + sinkra-map = 3 → extraído para security.sh"
    - "scoring engine: só validate-squad usa 9 dims + 7 guardrails = 1 → mantido inline"
    - "colors ANSI: 14 scripts usam = 14 → extraído para colors.sh"
```

## Decision Tree

```
IF (consumers >= 3 AND logic_is_generic)
  THEN extract to shared lib
ELSE IF (consumers == 2 AND logic_is_identical)
  THEN monitor, extract when 3rd appears
ELSE
  THEN keep inline — premature abstraction is worse than duplication
```

## Failure Modes

### O Módulo Shared que Ninguém Mais Usa
- **Trigger:** Scoring engine extraído para 1 consumidor "porque outros vão usar no futuro."
- **Manifestation:** Módulo shared com 1 consumidor + 7 guardrails que só fazem sentido pra esse consumidor.
- **Detection:** `grep -r 'require.*module' | wc -l` mostra 1 consumer.
- **Prevention:** Regra dos 3+. "NÃO extraído porque 1 consumidor com 7 guardrails específicos."

---

## Validation ✓

✅ **Paradoxo Identificado:** Abstraction Efficiency (reutilização via shared lib) vs. Pragmatic Coupling (manter inline para evitar overhead)

✅ **Tensão Sistêmica:** A heurística resolve o paradoxo via threshold quantitativo (3+ consumidores = ponto de inflexão onde abstração se justifica)

✅ **Aplicabilidade:** Validado em scoring engine (1 consumidor, mantido inline) + ANSI colors (14 consumidores, extraído)

✅ **Decisão Determinística:** Regra objetiva, sem ambiguidade interpretativa
