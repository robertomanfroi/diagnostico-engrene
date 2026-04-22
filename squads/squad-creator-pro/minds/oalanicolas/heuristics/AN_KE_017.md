# AN_KE_017 - Research No Meio, Não No Início

**Type:** Decision Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Timing Optimization
**Source:** [SOURCE: Epic 71 — tech-research feita após Wave 2, gerou 4 melhorias antes da Wave 3]
**sys_tension:** (no-research-early vs paralysis-cost, do-research-mid-cycle)

## Purpose

Research no início é paralisante (muitas opções, zero implementação). Research no meio é otimizante (já tem código, valida e melhora). Fazer entre Wave 2 e Wave 3.

## Configuration

```yaml
AN_KE_017:
  name: "Research No Meio"
  zone: "impacto"
  trigger: "Planejando quando fazer pesquisa/benchmarking"

  rule: |
    SE projeto tem múltiplas waves/fases
    NÃO pesquisar antes da Wave 1 (paralisa)
    PESQUISAR entre Wave 2 e Wave 3 (otimiza)
    PORQUE já tem implementação real pra comparar com estado da arte

  evidence:
    - "Wave 1+2: criou módulos + migrou sinkra squad"
    - "Research: confirmou alinhamento com Anthropic, achou 4 gaps"
    - "Wave 3: migrou cross-squad COM as 4 melhorias aplicadas"
    - "Se research fosse antes: 2h de análise sem código pra comparar"
```

## Decision Tree

```javascript
IF (planning_research_timing)
  Wave 1-2: BUILD first implementation (no research yet)
  BETWEEN Wave 2-3: RESEARCH state of the art
    COMPARE: your implementation vs industry best practices
    IDENTIFY: gaps to address in Wave 3
  Wave 3+: APPLY research findings to improve existing code
  NEVER: research before Wave 1 (paralizes with options)
  NEVER: research after final wave (too late to apply)
```

## Failure Modes

### A Paralisia por Análise
- **Trigger:** 2 horas pesquisando frameworks antes de escrever 1 linha.
- **Manifestation:** Análise extensa, zero implementação. Decision fatigue.
- **Detection:** Research duration > implementation duration at start of project.
- **Prevention:** Build first (waves 1-2), research mid-project (between 2-3), apply findings (wave 3+).

## Validation

**Paradoxo Identificado:** Research é essencial para decisões informadas, mas research antecipado paralisa a ação. A tensão é entre:
- **TENSION_WITH:** AN_KE_011 (Compare Antes de Construir) — Temporal Sequencing Inversion: AN_KE_011 demands research/comparison BEFORE implementation; AN_KE_017 mandates BUILD first, research/validation BETWEEN cycles
- **RESOLUTION:** "Pesquisa no meio ciclo valida implementação contra state-of-the-art enquanto código já existe pra comparar"

**Validação Empírica:** Epic 71 confirmou: research entre Wave 2-3 gerou 4 melhorias aplicáveis diretamente. Research antecipado teria consumido 2h sem contexto de implementação.

**Validação Processual:** A heurística foi testada em contexto de multi-wave planning e otimizou time-to-value vs decision quality.
