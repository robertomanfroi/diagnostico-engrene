# AN_KE_021 - Repair Layer Between Generator and Validator

**Type:** Architecture Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Defense in Depth
**Source:** [SOURCE: Sessao 2026-03-29 — yaml-repair.py desbloqueou Opus (0% → 67% completion)]
**sys_tension:** (Repair gratuito ($0) vs custo de implementar/manter worker determinístico | Resolver com automação open-source: json_repair (3M+ downloads), yaml-repair.py — um padrão já validado pela indústria)

## Purpose

Entre a geracao do LLM e a validacao, deve existir uma camada de repair deterministica. Repair e instantaneo e gratuito. Retry custa tokens e tempo.

## Configuration

```yaml
AN_KE_021:
  name: "Repair Layer"
  zone: "impacto"
  trigger: "Pipeline com LLM gerando structured output + validation"

  rule: |
    SEMPRE ter Worker de repair entre geracao e validacao
    Fluxo: LLM gera → repair (deterministic, $0) → validate → retry (se necessario)
    NUNCA validar output cru do LLM sem repair primeiro
    Repair e mais barato que 1 retry (tokens vs $0)

  anti_pattern: "Validar direto → falhar → retry → LLM gera mesmo erro → retry → circuit breaker"

  tension_with: "AN_KE_058 (Verify LLM Output) — Direct validation vs repair-then-validate"

  evidence:
    - "Opus sem repair: 0/9 fases (5 iteracoes desperdicadas na fase 1)"
    - "Opus com repair: 6/9 fases ($0.28, yaml-repair corrigiu 11 erros em <1s)"
    - "Haiku sem repair: 0/9 fases (nested quotes repetiam 5x)"
    - "Haiku com repair: 5/9 fases ($0.08)"
    - "json_repair (pip): 3M+ downloads/mes — industria ja usa este pattern"
    - "Custo de 1 repair: $0, <1s. Custo de 1 retry: ~$0.02-0.05, ~60s"

  architecture:
    flow: |
      LLM.generate()
        → repair_worker(output)     # $0, <1s, deterministic
          → schema_validate(output) # $0, <1s, deterministic
            → [PASS] use output
            → [FAIL] retry_with_error_context(max=3)  # $$ per retry
              → [STILL FAIL] fallback_model or escalate

    repair_types:
      json:
        library: "json_repair (pip)"
        fixes: "missing quotes, trailing commas, unescaped chars, incomplete objects"
      yaml:
        library: "yaml-repair.py (custom)"
        fixes: "colon-in-value, nested quotes, tabs→spaces, scalar-with-child"
      markdown:
        library: "none needed (tolerant format)"

  cost_comparison:
    without_repair:
      avg_retries: 2.5
      cost_per_retry: "$0.02-0.05"
      total_wasted: "$0.05-0.13 per phase"
      time_wasted: "150-300s per phase"
    with_repair:
      repair_cost: "$0"
      repair_time: "<1s"
      avg_retries: 0.3
      total_saved: "~$0.04-0.10 per phase"
```

## Decision Tree

```javascript
IF (pipeline_has_llm_generating_structured_output)
  CHECK: is there a repair layer between generate and validate?
    IF (NO) → ADD repair layer
    IF (YES) → verify it covers most common error types

  FLOW: LLM.generate() → repair($0, <1s) → validate($0) → [PASS|FAIL→retry($$)]

  REPAIR_TYPE_SELECTION:
    IF (json output) → use json_repair (pip, 3M+ downloads)
    IF (yaml output) → use yaml-repair.py (custom: colon-in-value, nested quotes)
    IF (markdown output) → no repair needed (tolerant format)

  NEVER: validate raw LLM output without repair first
  NEVER: use LLM for repair (defeats purpose — repair must be $0)
```

## Failure Modes

### O Opus que Custou 5x Mais
- **Trigger:** Opus generates YAML with syntax errors. No repair layer. 5 retries per phase.
- **Manifestation:** 0/9 phases completed. 5 iterations wasted on phase 1. Cost: $0.05-0.13/phase in retries.
- **Detection:** Retry rate > 2 per phase. Same error category repeating.
- **Prevention:** yaml-repair.py between generate and validate. 0% → 67% completion. Repair cost: $0, <1s.

## Validation

**Checkpoints:**
- [ ] Pipeline tem LLM gerando structured output (JSON/YAML)?
- [ ] Existe repair layer entre generate e validate?
- [ ] Repair é determinístico (não usa LLM)?
- [ ] Repair custa $0 e roda em <1s?
- [ ] Cobre json_repair (3M+ downloads) para JSON?
- [ ] Cobre yaml-repair.py para YAML?
- [ ] Retry só ocorre pós-repair e validation?
- [ ] Métricas rastreiam retry rate vs repair cost?

**Validação de Efetividade:**
- Baseline: Retry rate > 2 por phase = sinal de falta de repair
- Com repair: Retry rate cai para 0.3 por phase (90% redução)
- ROI: ~$0.04-0.10 economizado por phase em retries evitados
