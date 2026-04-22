# AN_KE_014 - Fan-out > Linhas Removidas

**Type:** Decision Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Correct ROI Metric
**Source:** [SOURCE: Epic 71 — net +345 linhas, mas 1 edit em state-manager.sh resolve 8 scripts]
**sys_tension:**
  - tension_with: "AN_KE_045 (Subtraction First Strategy) vs Fan-out Reduction"
  - resolution: "Fan-out (impacto de mudança) é a métrica verdadeira; mais linhas são aceitáveis se reduzem edições futuras (ROI temporal, não quantitativo)"

## Purpose

Shared infra sempre aumenta linhas totais no início. Medir sucesso por "linhas removidas" é a métrica errada. Medir por fan-out: quantos arquivos preciso editar quando algo muda.

## Configuration

```yaml
AN_KE_014:
  name: "Fan-out > Linhas Removidas"
  zone: "impacto"
  trigger: "Avaliando ROI de shared lib"

  rule: |
    SE avaliando se shared lib valeu a pena
    NÃO medir por linhas removidas (sempre negativo no início)
    MEDIR por fan-out de mudança: 1 edit → N scripts afetados

  metric:
    correct: "Fan-out de mudança (1 edit → N scripts)"
    incorrect: "Linhas removidas vs adicionadas"

  evidence:
    - "Epic 71: +501 linhas módulos, -156 linhas scripts = net +345"
    - "Mas: novo runtime = 1 edit em arg-parser.sh em vez de 8 edits"
    - "Bug fix = 1 fix em state-manager.sh em vez de caçar em 8 scripts"
```

## Decision Tree

```javascript
IF (evaluating_shared_lib_ROI)
  WRONG_METRIC: total_lines_after - total_lines_before  // Always negative initially
  RIGHT_METRIC: fan_out = files_that_need_editing_when_something_changes
    BEFORE shared lib: bug fix = edit N scripts individually
    AFTER shared lib: bug fix = edit 1 module, N scripts inherit
  IF (fan_out_reduction > 3x) → shared lib justified
  IF (fan_out_reduction < 2x) → reconsider extraction
```

## Failure Modes

### A Lib Shared que "Não Valeu a Pena"
- **Trigger:** Epic review mostra net +345 linhas. Stakeholder questiona ROI.
- **Manifestation:** "Adicionamos mais linhas do que removemos" — conclusão incorreta.
- **Detection:** Medindo ROI por diff size em vez de fan-out.
- **Prevention:** Medir fan-out: "1 edit em arg-parser.sh em vez de 8 edits" = 8x ROI real.

## Validation

**Paradox Resolution Validated:** A aparente contradição "mais linhas = mal" coexiste com "mais linhas = bom se reduz fan-out". A resolução está no shift de métrica: ROI não é quantidade de linhas, mas velocidade de mudança. Uma shared lib que adiciona 345 linhas mas reduz fan-out de 8→1 tem ROI massivo (8x retorno temporal). Métrica correta: `fan_out_reduction_ratio ≥ 3x` justifica investimento inicial em linhas.

**Evidence Chain:**
- Epic 71 net: +345 linhas totais
- Antes: bug fix = edit 8 scripts
- Depois: bug fix = edit 1 módulo, 8 scripts herdam → fan-out = 8x reduction
- Conclusão: ROI positivo apesar de linha count negativa

**Aplicability:** Decisões sobre shared libraries, refactoring, platform engineering.
