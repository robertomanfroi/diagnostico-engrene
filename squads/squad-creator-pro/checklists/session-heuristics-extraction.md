# Session Heuristics Extraction — Quality Gate Checklist

> **Process:** SP-EXTRACT-SESSION-HEURISTICS
> **Version:** 2.0.0
> **Agent:** @oalanicolas
> **Mode:** VALIDAR

---

## Phase 1: IDENTIFY — Varredura

- [ ] Sessão teve profundidade suficiente (≥ 5 candidatas brutas) [TKN-ESH-THR-002]
- [ ] As 5 categorias foram varridas:
  - [ ] Decisões pivot
  - [ ] Bugs/incidentes
  - [ ] Anti-patterns evitados
  - [ ] Patterns validados
  - [ ] Research insights
- [ ] Perguntas-guia CDM aplicadas (Critical Decision Method)
- [ ] Cada candidata tem pelo menos 1 frase de contexto

## Phase 2: FILTER — Pareto ao Cubo

- [ ] Classificação por zona aplicada (🔥 / 💎 / 🚀 / 💩)
- [ ] Ratio genérico ≤ 30% [TKN-ESH-THR-003]
- [ ] Teste de genericidade aplicado ("funciona sem contexto? → 💩")
- [ ] Candidatas 💩 descartadas com justificativa

## Phase 3: OVERLAP — Dedup

- [ ] Heurísticas existentes consultadas (`ls minds/oalanicolas/heuristics/`)
- [ ] Zero duplicatas criadas (overlap → update, não create) [TKN-ESH-BEH-001]
- [ ] Triangulação verificada (3+ sessões → promote zone) [TKN-ESH-BEH-002]

## Phase 4: FORMALIZE — Arquivos

- [ ] 100% das heurísticas têm [SOURCE:] rastreável [TKN-ESH-THR-001]
- [ ] Zero [INFERRED] sem evidência empírica
- [ ] Tipo válido usado [TKN-ESH-TAX-001]:
  - Decision | Veto | Architecture | Observability | State Management
- [ ] Formato padrão seguido:
  - [ ] Header (Type, Zone, Agent, Pattern, Source)
  - [ ] Purpose (1 frase)
  - [ ] Configuration YAML (name, zone, trigger, rule, evidence)
  - [ ] Decision Tree (IF/THEN/ELSE)
- [ ] Numeração contínua (sem gaps, sem sobreposição)
- [ ] anti_pattern documentado em cada heurística

## Phase 5: PERSIST — Commit

- [ ] MEMORY.md atualizado com referência
- [ ] Commit com mensagem padronizada: `feat(minds): add AN_KE_NNN-NNN ...`
- [ ] Push executado (se branch ativa)

---

## Gate Decision

| Score | Verdict |
|-------|---------|
| 15+ checks / 18 | **PASS** — extração aprovada |
| 12-14 / 18 | **WARN** — revisar items faltantes |
| < 12 / 18 | **FAIL** — re-executar fases fracas |

**Mínimo hard:** Phase 4 items 1-2 (source traceability) são BLOCKER. Se qualquer um falha, extração inteira falha.
