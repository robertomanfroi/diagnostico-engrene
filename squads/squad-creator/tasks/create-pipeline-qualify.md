# Task: Create Pipeline — Qualification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline-qualify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-pipeline-qualify
name: "Create Pipeline — Qualification"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o checklist de qualificação e veta scaffolding quando o squad não precisa de pipeline sequencial."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_pipeline_qualify
Output: artifact::create_pipeline_qualify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Determinar se o squad realmente precisa de pipeline multi-fase antes de gerar
qualquer scaffolding.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `requirements` | object | No | Briefing, sinais operacionais e contexto |
| `phase_definitions` | array | No | Lista preliminar de fases |

## Workflow

### Step 1: Aplicar checklist

Responder objetivamente às 5 perguntas da task composta:
- 3+ fases sequenciais
- >1 minuto por item
- dor de restart
- batch processing
- necessidade de custo por fase

### Step 2: Calcular score e decisão

Produzir score `0..5` e classificar:
- `3+` -> proceed
- `1-2` -> optional
- `0` -> veto

### Step 3: Emitir contrato

Gerar um `pipeline_qualification_contract` com score, evidências, decisão,
vetoes e recomendação de componentes básicos.

## Output

```yaml
pipeline_qualification_contract:
  decision: "proceed|optional|veto"
  score: 0
  evidence: []
  recommended_components: []
  veto_reason: null
```

## Acceptance Criteria

- [ ] Checklist executado com score `0..5`
- [ ] Decisão `proceed|optional|veto` emitida
- [ ] Evidências rastreáveis documentadas
- [ ] Veto explícito quando score = `0`

## Related Documents

- `create-pipeline.md`
- `create-pipeline-design.md`
- `data/pipeline-patterns.md`

---

_Task Version: 1.0.0_
