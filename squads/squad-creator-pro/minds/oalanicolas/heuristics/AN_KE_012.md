# AN_KE_012 - Batch Mecânico Primeiro, Hardening Depois

**Type:** Decision Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Triage by Root Cause
**Source:** [SOURCE: Story 70.3 — batch fix 29 frontmatters, 19% → 94% PASS em 5 minutos]
**Sys Tension:** (Speed vs. Completeness, Iterate mechanically first for quick wins, then invest in deep hardening)
**Sys Tension:** (Batch automation vs. Precision, Accept acceptable failure ratio from batch approach, prioritize architectural hardening for edge cases)

## Purpose

Quando uma base grande está falhando por motivo trivial (campo faltando, formato errado), corrigir o batch mecânico primeiro. Impacto desproporcional ao esforço. Hardening vem depois.

## Configuration

```yaml
AN_KE_012:
  name: "Batch Mecânico Primeiro"
  zone: "impacto"
  trigger: ">50% falhas com mesma root cause"
  tension_with: "AN_KE_025 (Determinism Over LLM) — batch aceitabilidade vs determinismo absoluto"

  rule: |
    SE >50% das falhas têm a mesma root cause trivial
    ENTÃO batch fix mecânico PRIMEIRO (impacto máximo, esforço mínimo)
    DEPOIS hardening (security, guardrails, deep checks)

  evidence:
    - "29/36 skills falhavam por 4 campos faltando no frontmatter"
    - "Batch fix: 5 min, script de 30 linhas. Resultado: 19% → 94%"
    - "Hardening posterior (T1_06, T1_07, guardrails): levou os 6% restantes"
```

## Decision Tree

```
IF (failure_rate > 50% AND root_cause_is_trivial)
  THEN batch_fix_mechanical → measure_improvement
  THEN hardening → measure_remaining_gap
ELSE
  investigate per-case
```

## Failure Modes

### Os 29 Frontmatters Quebrados
- **Trigger:** 29/36 skills falhando pelo mesmo campo faltando no frontmatter.
- **Manifestation:** 19% pass rate. Parece catastrófico mas root cause é trivial.
- **Detection:** > 50% falhas com mesma mensagem de erro.
- **Prevention:** Script de 30 linhas, 5 min fix → 94% pass. Hardening posterior para os 6% restantes.

## Validation

✅ **Paradox Identified:** The heuristic embodies the tension between *rapid mechanical batch remediation* (Speed) and *comprehensive quality hardening* (Completeness). By accepting 5-minute batch fixes with 19% baseline improvement, we sacrifice initial precision in exchange for systemic impact. The resolution is sequential iteration: batch first for volume, hardening second for robustness.

✅ **Sys Tension Resolution:**
- **Tension 1 (Speed vs. Completeness):** Resolved by *staged approach* — mechanical fixes unlock 75% gain immediately (19% → 94%), then architectural hardening captures residual 6% edge cases.
- **Tension 2 (Batch Automation vs. Precision):** Resolved by *acceptance criteria* — batch approach acceptable when single root cause affects >50% of population; precision hardening kicks in for heterogeneous failures.
