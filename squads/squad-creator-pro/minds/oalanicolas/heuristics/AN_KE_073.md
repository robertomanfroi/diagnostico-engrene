# AN_KE_073 - Parallel Subagents for Throughput
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mentelendaria 6c434ffc — "máximo de subagentes em paralelo"]

## Purpose

Quando tarefa é paralelizável (preenchimento de dados, pesquisa, validação, batch processing), usar o MÁXIMO de subagentes em paralelo. A IA por default executa sequencialmente — Alan exige paralelismo explícito para throughput. O padrão se aplica a LLM subagents (Claude workers), bash parallel jobs, e pipelines multi-fase. A distinção chave: paralelismo é para THROUGHPUT em tarefas independentes, não para colaboração em tarefas dependentes.

## Configuration

```yaml
AN_KE_073:
  name: "Parallel Subagents for Throughput"
  zone: "impacto"
  trigger: "Tarefa com múltiplos items independentes que podem ser processados em paralelo."
  sys_tension:
    tension_with: "PV_KE_088 (The Sequential Pipeline Truth) vs Complexidade de Parsing Local"
    resolution: "Paralelismo aplica-se a items INDEPENDENTES (sem dependência de estado prévio). Sequencialismo aplica-se a items DEPENDENTES (requerem output anterior como input). A decisão crítica: identificar se há dependência real entre items, não apenas processá-los na ordem."

  rule: |
    SE tarefa é paralelizável (items independentes, sem dependência entre eles)
    ENTÃO usar MÁXIMO de paralelismo disponível:
      - LLM: múltiplos subagentes simultâneos
      - Bash: parallel jobs, xargs -P, GNU parallel
      - Pipeline: fases independentes em paralelo
    Throughput > sequencialidade QUANDO items são independentes.
    NUNCA paralelizar tarefas com dependência entre elas.

  veto_condition:
    trigger: "Processando 10+ items sequencialmente quando são independentes."
    action: "VETO — 'FAça com o máximo de subagentes que conseguir.' Paralelizar."

  evidence:
    - "[SOURCE: sessão 6c434ffc, mentelendaria] 'FAça A com o máximo de subagentes que conseguir'"
    - "[SOURCE: sessão mentelendaria] 'use multiplos agentes em paralelo para este preenchimento e sempre pesquise na internet se tiver alguma dúvida'"
    - "[PATTERN] Modelo wave-based em story-cycle usa parallelismo headless (claude -p em worktrees separados)"
    - "[SOURCE: sessão e0a18d13, mmos] 'revise um a um, use multiplos agentes para ser mais rápido'"
    - "[SOURCE: sessão b89fe039, mmos] 'Use multiplos agentes e faça todas atividades paralelas que puder'"
    - "[SOURCE: sessão 24a4da7c, mmos] 'Quero testar o modo paralelo com 10 livros usando gemini e subagents'"
```

## Decision Tree

```javascript
IF (batch_of_independent_items)
  STEP_1: CHECK independence
    IF (item_N depends on item_N-1) → SEQUENTIAL (cannot parallelize)
    IF (items are independent) → PARALLELIZE

  STEP_2: SELECT parallelism method
    IF (LLM processing) → spawn N subagents, each with 1 item
    IF (bash/script) → xargs -P $(nproc) or GNU parallel
    IF (multi-phase pipeline) → check which phases are independent

  STEP_3: FAN-OUT
    LIMIT: respect rate limits / billing limits (AN_KE_064)
    TRACK: progress per parallel worker
    COLLECT: results after all complete

  STEP_4: FAN-IN
    MERGE: individual results into unified output
    VALIDATE: completeness (all items processed?)
    REPORT: failures per worker

  NEVER: process 10+ independent items one-by-one
  EXCEPTION: when debugging, sequential is fine for visibility
```

## Failure Modes

### O Preenchimento de 200 Campos em Série
- **Trigger:** 200 dados de personas para preencher → IA processa 1 por vez.
- **Manifestation:** Task que deveria levar 5 minutos leva 2 horas.
- **Detection:** Monitoramento mostra: 1 request/min para tarefa batch-friendly.
- **Prevention:** "FAça com o máximo de subagentes." Fan-out/fan-in pattern.

## Validation

**✓ Heurística validada**

| Critério | Status | Nota |
|----------|--------|------|
| Paradoxo identificado | ✓ | Tensão entre paralelismo (independência) e sequencialismo (dependência) |
| Resolução clara | ✓ | Critério de decisão: presença/ausência de dependência de estado |
| Aplicabilidade | ✓ | Claramente aplicável a batch processing, pesquisa, validação, preenchimento de dados |
| Evidência | ✓ | 6 fontes diretas de Alan e padrão wave-based documentado |
| Integração com AN_KE_038 | ✓ | Complementária, não conflitante; define espaço de aplicação diferente |

**Paradoxo resolvido:** A tensão entre "sempre paralelizar" e "manter contexto sequencial" resolve-se na **análise de dependência de estado**. Se não há dependência, paraleliza; se há, mantém sequência com contexto preservado (AN_KE_038).
