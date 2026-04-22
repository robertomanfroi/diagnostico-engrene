# AN_KE_065 - Model Quality Gap is Real
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub b3c022b9 — benchmark sinkra-map Gemini vs Claude]

## Purpose

A variância de qualidade entre modelos para a MESMA tarefa é enorme, mensurável, e não é bug — é feature do mercado. Benchmark real: Gemini 45/100 vs Claude 84/100 para o mesmo squad, mesmo prompt, mesmo input. Gap de 39 pontos. Mas o problema vai além do score: Alan questionou se o Gemini sequer completou o pipeline ("gemini nao rodou todo pipeline rodou?"). O gap não é só de qualidade — é de COMPLETUDE. Modelos inferiores podem pular steps, gerar output parcial, ou seguir instruções seletivamente. Validação DEVE ser model-aware em ambas dimensões: qualidade E completude.

## Configuration

```yaml
AN_KE_065:
  name: "Model Quality Gap is Real"
  zone: "impacto"
  trigger: "Usando múltiplos modelos para mesma tarefa, validando output de LLM, ou selecionando modelo para nova task."

  rule: |
    SE usando múltiplos modelos para mesma task
    ENTÃO esperar variância GRANDE de qualidade (40+ pontos possível).
    Gap não é só score — é completude (pipeline parcial vs completo).
    Validação DEVE ser model-aware em 2 dimensões:
      (1) Quality score — threshold ajustado por modelo
      (2) Completeness — todas as phases/steps foram executadas?
    Benchmark ANTES de confiar em output de modelo novo.

  veto_condition:
    trigger: "Aceitar output de modelo sem benchmark, ou tratar output parcial como completo."
    action: "VETO — Benchmark primeiro. 'pq tao diferente?' Compare contra golden sample E verifique completude."

  sys_tension:
    tension_with: "AN_KE_064 (Model Tier Fallback) — vs confiança implícita em modelos LLM (expectativa de completude 100% e qualidade consistente)"
    resolution: "Instituir desconfiança ativa: benchmark obrigatório antes de usar novo modelo, verificação de completude ANTES de quality scoring, validação model-aware em ambas dimensões"

  evidence:
    - "[SOURCE: sessão b3c022b9, sinkra-hub] 'gemini nao rodou todo pipeline rodou? pq tao diferente? 45/100 vs Claude 84/100 pro mesmo squad?'"
    - "[DATA] Benchmark sinkra-map: mesmo input, mesmo prompt, Gemini=45/100 Claude=84/100 — gap de 39 pontos no mesmo squad"
```

## Decision Tree

```javascript
IF (multi_model_pipeline OR validating_llm_output)
  STEP_1: BENCHMARK each model against golden sample
    RUN: same input, same prompt, 3+ iterations
    RECORD: (quality_score, completeness_%, latency, cost) per model per task_type

  STEP_2: CHECK completeness FIRST
    COUNT: phases completed / phases expected
    IF (completeness < 100%) → FLAG as partial output
    IF (completeness < 70%) → REJECT regardless of quality score
    THEN: evaluate quality score on complete outputs only

  STEP_3: SET model-aware thresholds
    IF (model_A avg_score ~85, completeness 100%) → quality threshold = 75
    IF (model_B avg_score ~45, completeness 80%) → EXCLUDE from pipeline OR use only for low-complexity tasks
    RELATIONSHIP: feeds into AN_KE_064 tier list

  STEP_4: VALIDATE output against correct threshold
    IF (below_threshold OR incomplete) → retry with higher-tier model
    IF (above_threshold AND complete) → accept with model tag in metadata
  NEVER: assume Model A quality ≈ Model B quality without benchmark data
```

## Failure Modes

### O Squad Fantasma (Incompleto mas Aceito)
- **Trigger:** Gemini gera squad com score 45/100 mas pipeline aceita sem verificar completude.
- **Manifestation:** Squad parece completo mas phases 5-7 foram skippadas. Tasks referencing ausentes.
- **Detection:** Score baixo E/OU diff de structure vs golden sample mostra seções inteiras faltando.
- **Prevention:** Completeness check ANTES de quality scoring. Se model não completou pipeline → não pontuar, rejeitar.

## Validation

**Paradoxo Identificado:** Para usar modelos LLM com segurança, é necessário desconfiar deles. A heurística resolve esta tensão instituindo desconfiança ativa (benchmark, completeness check) como precondição para aceitação de output.

**Checkpoints de Validação:**
1. ✅ Benchmark obrigatório contra golden sample (3+ iterações, mesmo prompt/input)
2. ✅ Completude verificada ANTES de quality scoring (phases/steps completos ≥70%, rejeitar <70%)
3. ✅ Thresholds model-aware (Claude ~85 → threshold 75; Gemini ~45 → EXCLUDE ou tasks baixa complexidade)
4. ✅ Metadata com model tag em outputs aceitos
5. ✅ Verificação diff estrutural vs golden sample (seções inteiras faltando = rejeição)

**Casos de Uso Validados:**
- Multi-model squad generation (AN_KE_064 tier list)
- LLM output validation pipelines
- Model selection para novas tasks
- Quality assurance em workflows com múltiplos LLMs
