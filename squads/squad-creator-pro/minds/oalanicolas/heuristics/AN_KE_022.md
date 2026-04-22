# AN_KE_022 - Format Follows Generator

**Type:** Architecture Heuristic
**Zone:** 🔥 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Output Format Selection
**Source:** [SOURCE: Sessao 2026-03-29 — benchmark 4 modelos SINKRA map-process, migracao YAML→JSON]

```yaml
sys_tension:
  tension_with: "AN_KE_021 (Repair Layer Between Generator and Validator) vs Format Mutation Cost"
  conflict: "JSON is 5x safer for LLM generation (98% validity vs 0% YAML errors), but YAML is +11.8pp better for human consumption"
  resolution: "Use generator format for creation (JSON), convert deterministically to consumer format (YAML/MD) post-generation. Generator safety trumps consumer preference at creation time."
  trade_off: "Accept JSON-to-YAML conversion overhead to eliminate 5x retry cost. Cost of failed generation >> cost of deterministic conversion."
```

## Purpose

O formato de output deve ser escolhido pela capacidade do gerador, nao pela preferencia do consumidor. Gerar no formato mais seguro e converter no destino.

## Configuration

```yaml
AN_KE_022:
  name: "Format Follows Generator"
  zone: "genialidade"
  trigger: "Escolhendo formato de output pra LLM"

  rule: |
    SE LLM gera o output → JSON (sintaticamente rigido, sem ambiguidade)
    SE humano consome → converter JSON→YAML/MD no destino (deterministico)
    NUNCA pedir pro LLM gerar no formato de consumo se existe formato mais seguro

  evidence:
    - "3/4 erros YAML nao existem em JSON (colon-in-value, nested quotes, indentation)"
    - "Opus 0% completion com YAML vs ~98-100% JSON validity"
    - "Haiku bloqueio 100% por YAML, nao por capacidade"
    - "StructEval 2025: JSON generation >90% validity; YAML melhor pra leitura (+11.8pp)"
```

## Decision Tree

```javascript
IF (choosing_output_format_for_llm)
  STEP_1: WHO generates? LLM or deterministic code?
    IF (LLM) → JSON (syntactically rigid, no ambiguity)
    IF (code) → any format (deterministic = no risk)
  STEP_2: CONSUMER needs different format?
    IF (yes) → convert JSON→YAML/MD deterministically POST-generation
    IF (no) → keep as JSON
  STEP_3: COST of format failure?
    YAML: ~5x retry rate (colon-in-value, indentation, nested quotes)
    JSON: ~0.3x retry rate (syntactically strict)
  NEVER: ask LLM to generate in consumer format if safer format exists
```

## Failure Modes

### O Opus que Não Completou (0% YAML)
- **Trigger:** Asking Opus to generate YAML output for squad config.
- **Manifestation:** 0% completion rate. Every response has YAML syntax errors.
- **Detection:** Opus $0.28/run with 0% usable output vs JSON at ~98% validity.
- **Prevention:** Format Follows Generator. LLM → JSON → convert to YAML deterministically.

---

## Validation

**Paradox Identified:** Security vs. Usability trade-off
- **JSON Generation Security:** 98% validity rate, 0.3x retry factor
- **YAML Readability:** +11.8pp human comprehension improvement
- **Resolution Proof:** Deterministic JSON→YAML conversion eliminates both risks (safe generation + usable output)
- **Evidence:** 4-model benchmark (Opus, Sonnet, Haiku, Quantized) shows 100% YAML blocker but 5x JSON success with conversion overhead < generation retry cost

**Status:** ✓ Validated via empirical benchmark data and failure mode analysis
