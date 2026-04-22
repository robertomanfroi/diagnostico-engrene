# AN_KE_064 - Model Tier Fallback
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões sinkra-hub b3c022b9, mmos 53066af4, b6ad4eab — billing limit + fallback architecture discussions]

## Purpose

Pipelines que dependem de LLM DEVEM ter fallback entre modelos — mas o fallback não é apenas "próximo na lista". Alan especifica dois eixos: (1) fallback por DISPONIBILIDADE (billing/rate limit/outage → próximo provider), e (2) fallback por QUALIDADE (modelo com melhor score para aquela task específica). A visão é um banco de dados per-task com o melhor modelo para cada tipo de tarefa, começando como YAML e evoluindo para SQL. O fallback é model-aware E task-aware.

## Configuration

```yaml
AN_KE_064:
  name: "Model Tier Fallback"
  zone: "excelencia"
  trigger: "Pipeline ou workflow que usa LLM como step de execução sem fallback chain definida."

  rule: |
    SE pipeline usa LLM como executor
    ENTÃO DEVE ter:
      (1) Tier list de disponibilidade: primary → secondary → tertiary
      (2) Banco task-aware: cada task tem ranking de modelos por qualidade
      (3) Critérios de seleção: língua (PT-BR proficiency), contexto (window size), custo
    NUNCA abortar pipeline por failure de um único provider.
    Começar com YAML, evoluir para SQL quando tiver dados suficientes.

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents) vs Complexidade de Parsing Local"
    resolution: |
      AN_KE_064 (availability/tier fallback) vs AN_KE_065 (quality threshold retry):
      - AN_KE_064: fallback por FALHA (billing limit, outage, rate limit)
      - AN_KE_065: retry por QUALIDADE (output abaixo do threshold)
      RESOLUÇÃO: Aplicar em sequência — tenta AN_KE_064 (10s de latência), se passa em qualidade vai embora;
      se falha em qualidade, aplica AN_KE_065 com modelo de maior tier.

  veto_condition:
    trigger: "Pipeline com single-model dependency OU fallback genérico sem considerar task-specific quality."
    action: "VETO — Defina tier list task-aware. 'pra cada task, vamos ter um banco de dados com os melhores modelos.' Teste cada tier."

  evidence:
    - "[SOURCE: sessão b3c022b9, sinkra-hub] 'precisamos de fallback entre os modelos, exemplo do codex aqui agora: FATAL: Usage/billing limit reached. Aborting.'"
    - "[SOURCE: sessão 53066af4, mmos] 'vamos fazer 2 camadas de fallback, qual seria o melhor modelo, considerando seu conhecimento em portugues e tamanho de janela de contexto?'"
    - "[SOURCE: sessão 53066af4, mmos] 'para cada task, vamos ter um banco de dados com os melhores modelos específicos para aquela task, podemos começar com um YAML'"
    - "[SOURCE: sessão b6ad4eab, mmos] 'precisamos descobrir outro modelo do openrouter para compor nosso fallback 1 ou 2 dependendo da nota que alcançarmos'"
    - "[SOURCE: sessão decoder.sh mmos+squad_creator run] 'Cascade confirmado em produção: haiku falha (Prompt is too long, 1.46M tokens → 200K context) → runner-lib fallback Gemini Pro (2M context) → Gemini ESCREVE 9-15 arquivos com Write tool. Com --max-turns 5, haiku cabe no context → fallback raro.'"
```

## Decision Tree

```javascript
IF (pipeline_uses_llm)
  REQUIRE: model_tier_config (YAML or DB)

  STEP_1: SELECT model for task
    LOOKUP: task_type → ranked model list (quality-based)
    CRITERIA: (1) quality score for this task type, (2) PT-BR proficiency, (3) context window
    IF (no task-specific ranking) → USE default tier list

  STEP_2: EXECUTE with selected model
    ON_SUCCESS → log model + score for future ranking

  STEP_3: ON_FAILURE, cascade fallback
    IF (billing_limit) → next tier, log degradation warning
    IF (rate_limit) → exponential backoff 3x, then next tier
    IF (outage) → immediate switch to next tier
    IF (quality_below_threshold) → retry with higher-tier model (AN_KE_065)

  STEP_4: ALL_TIERS_EXHAUSTED
    → queue for retry with delay
    → notify human
    → NEVER abort with partial work lost

  DATA_EVOLUTION:
    Phase 1: routing.yaml (static per-task ranking)
    Phase 2: benchmark results inform ranking updates
    Phase 3: SQL table with historical quality scores per model per task
```

## Failure Modes

### O Pipeline que Para às 3h da Manhã
- **Trigger:** Pipeline autônomo (sinkra-map.sh) rodando overnight atinge billing limit do Codex.
- **Manifestation:** "FATAL: Usage/billing limit reached. Aborting." — Phase 1 nem completou. Trabalho parcial perdido.
- **Detection:** Pipeline log mostra abort na primeira iteração sem tentativa de fallback.
- **Recovery:** `--phase 1` flag permite resume, mas trabalho da iteração é perdido.
- **Prevention:** Tier list: Codex → Claude → Gemini. Cada tier testado com benchmark antes de entrar na lista. YAML do routing atualizado com scores.

## Validation

### Checklist de Implementação
- [ ] Tier list definida com pelo menos 3 modelos ordenados por disponibilidade/qualidade
- [ ] Arquivo `routing.yaml` criado com task-specific model rankings
- [ ] Cada tier testado com benchmark antes de validação
- [ ] Critérios de seleção documentados (PT-BR proficiency, context window, custo)
- [ ] Decision tree implementado com cascata de fallback
- [ ] Logging de tentativas de fallback em cada etapa
- [ ] Timeout e exponential backoff configurados para rate limits
- [ ] Teste E2E com simulação de falha de cada tier
- [ ] Integração com AN_KE_065 (quality threshold retry) validada
- [ ] Documentação de data evolution phases (YAML → SQL) atualizada

### Critérios de Sucesso
**✓ Paradoxo resolvido:** Disponibilidade (AN_KE_064) + Qualidade (AN_KE_065) trabalham em sequência sem conflito de interesses.

**✓ Garantias de resiliência:** Pipeline NUNCA aborta com trabalho parcial perdido — fallback automático até esgotar tiers ou enfileirar com delay.

**✓ Data-driven evolution:** YAML inicial alimenta histórico de sucesso/falha por task-type; SQL evolui conforme acumular scores.
