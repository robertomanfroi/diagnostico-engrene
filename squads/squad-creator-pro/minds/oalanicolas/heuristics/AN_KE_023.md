# AN_KE_023 - Tier System e Invisivel

**Type:** Observability Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Pattern:** Transparency in Abstraction
**Source:** [SOURCE: Sessao 2026-03-29 — --model haiku resolvia pra opus silenciosamente]
**sys_tension:** (transparency vs. resource optimization, resolve via explicit logging + user control)

## Purpose

Abstracoes de routing devem ser transparentes. Se o usuario pede haiku e recebe opus, a abstracao falhou. Todo override deve ser logado.

## Configuration

```yaml
AN_KE_023:
  name: "Tier System e Invisivel"
  zone: "excelencia"
  trigger: "Implementando abstracao de routing (modelo, runtime, provedor)"

  rule: |
    SE abstracao sobrescreve decisao do usuario → LOGAR explicitamente
    SEMPRE logar modelo REAL, nao o pedido
    OFERECER bypass explicito (--force-model)

  tension_with: "AN_KE_106 (Subagents Over Flattened Tasks) — Abstrações de routing para ganho de throughput vs Transparência de recursos"

  evidence:
    - "--model haiku resolvia pra opus nas fases high (tier system silencioso)"
    - "Benchmark 'Haiku' $0.29 = 'Opus' $0.28 — eram o mesmo modelo"
    - "Fix: --force-model + log do modelo real por fase"
```

## Decision Tree

```javascript
IF (implementing_routing_abstraction: model, runtime, provider)
  REQUIRE: log ACTUAL resource used (not just requested)
  REQUIRE: log OVERRIDE if abstraction changed user's choice
  REQUIRE: --force-{resource} bypass flag
  IF (user_request != actual_used) → LOG: "Requested: X, Used: Y, Reason: Z"
  NEVER: silently substitute without logging
```

## Failure Modes

### O Benchmark que Cusava o Dobro
- **Trigger:** `--model haiku` silently routed to opus. Benchmark showed haiku $0.29 ≈ opus $0.28.
- **Manifestation:** "Eram o mesmo modelo" — tier system invisible, costs hidden.
- **Detection:** Cost analysis shows haiku suspiciously expensive. Same price = same model.
- **Prevention:** Log real model per phase. `--force-model` bypass for benchmarking.

## Validation

✓ **Paradox Identified:** Abstraction (routing optimization) contradicts transparency (user must know what runs). User requests haiku for cost control, system substitutes opus, cost remains similar (masking the swap).

✓ **Tension Resolved:** Explicit logging of actual model used + `--force-model` flag restores user control while allowing optimization. When costs are identical, transparency reveals the truth.

✓ **Heuristic Sound:** Applies to any routing layer (model, runtime, provider). Prevention requires dual mechanism: logging + user override.
