# AN_KE_016 - Testar Módulo Isolado, Não Pipeline

**Type:** Decision Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Test Isolation
**Source:** [SOURCE: Epic 71 — bug ${} quoting encontrado em 2s pelo test suite, não em 30min de pipeline]
**sys_tension:**
  - tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Isolamento Sequencial de Módulos"
    resolution: "Testes isolados em <5s MAIS regressão cíclica (1/semana) vs pipeline contínuo. Isolado evita falsos-negativos de performance; pipeline evita falsos-positivos de integração"

## Purpose

Cada módulo shared deve ter smoke test que roda em <5s sem dependências externas. Se precisa rodar pipeline completo pra testar uma função, a função está mal isolada.

## Configuration

```yaml
AN_KE_016:
  name: "Testar Módulo Isolado"
  zone: "impacto"
  trigger: "Testando módulo shared ou função extraída"

  rule: |
    SE módulo shared criado/modificado
    ENTÃO smoke test isolado em <5s (sem LLM, sem rede, sem squad)
    SE precisa do pipeline completo pra testar → função mal isolada, refatorar

  evidence:
    - "Bug $\{} quoting: encontrado pelo test suite 30s, não pelo sinkra-map 30min"
    - "94 testes rodando em 30s = 19 syntax + 12 bootstrap + 10 json + 9 state + 8 smoke + 36 skills"
    - "Debug isolado: 2s. Debug em pipeline: 10-30min"
```

## Decision Tree

```javascript
IF (testing_shared_module)
  REQUIRE: smoke test that runs in <5s
    NO LLM dependency
    NO network dependency
    NO squad/pipeline dependency
  IF (test requires full pipeline) → module is poorly isolated → REFACTOR
  IF (test runs standalone in <5s) → module is well-isolated → PASS
```

## Failure Modes

### O Bug que Levou 30min pra Achar
- **Trigger:** `${variable}` quoting bug in shared function. Tested via full pipeline.
- **Manifestation:** 30 min debugging pipeline logs to find 1-character bug.
- **Detection:** Test suite would find it in 2 seconds.
- **Prevention:** Smoke test isolado. 94 testes em 30s catch o que pipeline levaria 30min.

---

## Validation

✅ **Paradoxo Identificado:** Isolamento X Integração
- **Isolado:** Rápido (2s), mas não valida dependências reais
- **Pipeline:** Lento (30min), mas mascara bugs locais em ruído de logs

✅ **Resolução:** Camadas — Isolado (smoke) + Semanal (full pipeline) + Contínuo (regressão por feature)

✅ **Evidence Linking:** Bug ${} seria encontrado em 2s, não 30min

✅ **Actionable:** IF módulo compartilhado THEN <5s smoke test SEM exceção
