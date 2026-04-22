# AN_KE_097 - Fail-Safe Small Batches
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 6dd07098, mmos — "vamos de 3 em 3 para dar menos risco pro erro"]

## Purpose

Migração ou mutação global de alto risco gera desgaste cognitivo se causar "crash-and-burn" fatal e destruir toda a chain da sessão. Mutações pesadas devem abraçar segurança de escopo por parcelamento (batching). Seja copiando código complexo de migrations pro humano testar, seja varrendo 100 livros (executando aos poucos). Processos críticos precisam ser expostos e verificados ao Humano "de pedaço em pedaço". Reduz carga contextual, zera chance de travar a base com mil erros simultâneos.

## Configuration

```yaml
AN_KE_097:
  name: "Fail-Safe Small Batches"
  zone: "impacto"
  trigger: "Reescritas massivas de banco de dados, aplicação ou exportando transições grandes em copypast para terminal."

  rule: |
    SE a operação em andamento envolve volume grande e é arriscada (ex: migrations de sql, correções de centenas de arquivos)
    ENTÃO subdivida a entrega ou o processamento em lotes extremamente conservadores (ex: batch de 3).
    Menor risco = Maior recuperabilidade do log local caso rompa o context window com excesso de falhas.

  veto_condition:
    trigger: "Agente imprime um bloco SQL de 500 linhas que afeta 14 tabelas simultâneas de reestruturação de chave complexa sem aviso ou particionamento."
    action: "VETO — 'vamos de 3 em 3 para dar menos risco pro erro?'."

  evidence:
    - "[SOURCE: sessão 6dd07098] 'vamos de 3 em 3 para dar menos risco pro erro? copie 3 migrations aqui para meu copypast'"

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs. Sequential Small Batch Safety"
    resolution: "Prioritize atomic verification over throughput. Each batch MUST be validated before proceeding, even if total time increases. Recovery from a failed monolithic delivery > time cost of batch sequencing."
```

## Decision Tree

```javascript
IF (generating_highly_complex_or_risky_data)
  STEP_1: QUANTIFY scope of change.
    IF (volume > safe_tolerance_limit) -> SPLIT INTO CHUNKS.
  STEP_2: CHUNK 1 (Provide Batch 1 of N)
    Example: Deliver 3 SQL migrations out of 10.
  STEP_3: AWAIT validation execution test.
  STEP_4: IF Success -> Proceed to Next Batch.
```

## Failure Modes

### Monolithic Crash Delivery
- **Trigger:** Agente entende o pedido de tradução completa de 8 docs e queima todo a janela em 9800 linhas massivas que param no meio pelo limítrofe falhando pela metade.
- **Manifestation:** Arquivos quebrados, perda do log histórico por excesso de output (blooming window).
- **Prevention:** "Divide and Conquer". O Humano processa por etapas sem ansiedade fatal.

## Validation

**Paradox Identified:** Small batches slow immediate output but guarantee system integrity. Safety via constraint > convenience via speed.

**When to Apply:** Any operation affecting >10 files, >5 tables, >100 lines of critical code, or migrations that cannot be easily rolled back.

**Success Criteria:**
- Each batch completes without context window pressure
- Human can validate and approve before next batch
- No failures cascade across batches
- Recovery is always within reach
