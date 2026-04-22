# AN_KE_111 - Day 0 Million-Scale Mindset
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 33889e33, aiox-stage — "preparada para 1 milhao para evitar retrabalhos globais"]

## Purpose

Na startup culture, a ideia de "fazer só pro showcase de hoje" é sedutora. O problema do *Hardcoding* frágil é que, quando os primeiros 1.000 usuários atritarem com o sistema, ele derretera como manteiga no Supabase (se você buscou todos os cursos fazendo requisição full O(N)). O Alan determina implacavelmente que arquiteturas raiz (Indexações no Prisma, Policies Base de RLS, Filas Assíncronas) não têm a permissão de serem lançadas débeis. Desenhe e execute matematicamente provando que resistirá a 1 Milhão no tráfego cronológico para congelar dívidas precoces.

## Configuration

```yaml
AN_KE_111:
  name: "Day 0 Million-Scale Mindset"
  zone: "genialidade"
  trigger: "Configuração de roteadores vitais Node.js, queries primárias Supabase/Prisma ou Eventos Cron."

  rule: |
    SE programar chamadas fundamentais que afetam o core render (ex: `Select` massivo, `Array.map` iterativo global)
    ENTÃO DEVE justificar sua escalabilidade assintótica ou arquitetar a query (Pagination, Indexes, RLs blindado)
    para sobreviver a Carga Teórica de "1 Milhão" instantânea.
    O VETO é para "vamos mockar primeiro e ver como agride o servidor depois".

  veto_condition:
    trigger: "Agente cria a HomePage do MMOS disparando 3 chamadas HTTP no `useEffect` pedindo a lista completa de TODOS os cursos e seus sub-módulos em O(1)."
    action: "VETO — 'vamos comecar agora com 1000 acessos mas pensando e com a base preparada para 1 milhao para evitar retrabalhos futuros. e com custos baixos.'."

  sys_tension:
    tension_with: "AN_KE_017 (Research No Meio, Não No Início) vs Complexidade de Análise Assintótica (Parsing Local); AN_KE_049 (Ship First, Doc Later) — velocidade vs escalabilidade"
    poles:
      pole_a:
        name: "Ship Fast (MVP mindset)"
        implication: "Solução rápida, frágil em escala, retrabalho futuro"
      pole_b:
        name: "Build for Scale (Day 0 preparation)"
        implication: "Investimento inicial maior, solidez comprovada, sem débito técnico"
    resolution: |
      O paradoxo é falso. Escalabilidade não é over-engineering cosmético — é o custo INICIAL de
      arquitetura (indexes, pagination, RLS) que evita retrabalho exponencial posterior.
      Resolução: Diferenciar entre MVP "quick/dirty" (aceitável em UI/UX) e MVP "architected"
      (obrigatório em queries/dados/APIs). Query O(N) em 1.000 usuários → mata-se em 1.000.000.
    metric: "Ask: 'Will this code survive 1M concurrent requests?' If NO → Refactor before shipping."
    severity: "CRITICAL"
    recurrence: "Every data-fetching decision"

  evidence:
    - "[SOURCE: sessão 33889e33, aiox-stage/scale] 'vamos comecar agora com 1000 acessos mas pensando e com a base preparada para 1 milhao para evitar retrabalhos futuros. e com custos baixos.'"
```

## Decision Tree

```javascript
IF (writing_global_query_or_ingesting_large_arrays_to_FE)
  STEP_1: CHALLENGE Big O Complexity. Is it querying the whole table or mapping without pagination?
  STEP_2: IF YES (It fetches all `users` indiscriminately)
    -> REWRITE using native SQL row limits (`.range()`, `.limit()`) OR server-side cursor pagination.
  STEP_3: IMPLEMENT strict foreign keys and Postgres Indexes on `created_at` or heavily sorted columns.
  STEP_4: Assume heavy traffic is current.
```

## Failure Modes

### Memory Leak de MVP
- **Trigger:** Fetch ingênuo de todos os logs do Slack pra "testar a visualização das métricas da comunidade". O array atinge 5.000 entradas.
- **Manifestation:** React crashea imediatamente com *Out Of Memory* no Edge Lambda do Vercel. O desenvolvedor perde 3 dias só otimizando VDOM e descobrindo paginação que devia ter nascido no dia zero.
- **Prevention:** Pagination Limit hardcoded Day-1.

---

## Validation

| Criterion | Status | Notes |
|-----------|--------|-------|
| **Paradox Identified** | ✅ | MVP Speed vs. Scalable Architecture — false tension resolved through architectural hygiene |
| **System Tension Documented** | ✅ | sys_tension field includes both poles, resolution, and metric for validation |
| **Decision Tree Complete** | ✅ | 4-step flow: Challenge Big O → Check limits → Implement indexes → Assume heavy load |
| **Failure Mode Mapped** | ✅ | Memory Leak of MVP demonstrates cost of deferring scalability |
| **Enforcement Metric** | ✅ | "Will this code survive 1M concurrent requests?" — testable veto condition |
| **Resolution Actionable** | ✅ | MVP "architected" path defined — queries must prove scalability, UI can be quick |
| **Integration Verified** | ✅ | Cross-reference with AN_KE_049 acknowledged; complementary not contradictory |
| **Severity & Recurrence** | ✅ | CRITICAL — applies to every data-fetching decision in Day 0 |

**Assessment:** APPROVED for operational use. Core principle: Architectural decisions have cascading costs. Build defensively from Day 0 on data layer; UI velocity is secondary.

---

**Pattern Compliance:** Day 0 Million-Scale Mindset
**System Tension:** Speed (Ship) vs Scalability (Build defensible) — resolved via differential treatment
**Integration:** Critical checkpoint for database design, query patterns, API endpoints
