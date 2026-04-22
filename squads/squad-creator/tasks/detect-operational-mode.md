# Task: Detect Operational Mode (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `detect-operational-mode` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: detect-operational-mode
name: "Detect Operational Mode"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Composed task that orchestrates 5 atomic sub-tasks to classify a squad as OPERATIONAL or TEXTUAL."
owner_workflow: "workflows/wf-detect-operational-mode.yaml"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::detect_operational_mode
Output: artifact::detect_operational_mode
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Classificar o briefing do squad em `OPERATIONAL` ou `TEXTUAL` usando sinais de
verbos, sistemas externos e outputs esperados. Quando o modo for operacional,
emitir também o contrato de infraestrutura consumido por `setup-runtime` e
`operational-test`.

## Execution Sequence

```
INPUT (briefing + outputs_defined + skills_detected)
    |
[1] detect-operational-mode-verbs
    -> Sinal lexical: verbos operacionais vs textuais
    |
[2] detect-operational-mode-systems
    -> Sinal de integrações, APIs e serviços externos
    |
[3] detect-operational-mode-outputs
    -> Sinal de outputs reais vs artefatos textuais
    |
[4] detect-operational-mode-classify
    -> Score final, vetoes e mode_report
    |
[5] detect-operational-mode-infrastructure
    -> Plano de runtime e próximos ativos operacionais
    |
OUTPUT: mode_report + infrastructure_plan
```

## Sub-Task Reference

| # | Task ID | Phase | Responsibility | Executor |
|---|---------|-------|----------------|----------|
| 1 | `detect-operational-mode-verbs` | Signal Extraction | Ler briefing e extrair verbos | Worker |
| 2 | `detect-operational-mode-systems` | Signal Extraction | Detectar plataformas e conexões | Worker |
| 3 | `detect-operational-mode-outputs` | Signal Extraction | Classificar outputs esperados | Worker |
| 4 | `detect-operational-mode-classify` | Classification | Calcular score, vetoes e relatório | Agent |
| 5 | `detect-operational-mode-infrastructure` | Infrastructure | Emitir contrato de APIs e runtime | Agent |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `briefing` | string | Yes | Briefing bruto do squad |
| `outputs_defined` | list | Yes | Outputs detectados na criação |
| `skills_detected` | list | No | Skills já detectadas |
| `squad_name` | string | No | Nome do squad alvo |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| `mode_report` | `runtime_context` | Relatório consolidado do modo |
| `infrastructure_plan` | `runtime_context` | Plano de APIs, env vars e assets |
| API Requirements | `squads/{squad_name}/data/api-requirements.yaml` | Consumido depois por setup-runtime |

## Veto Conditions

- Sem verbos acionáveis e sem outputs definidos -> bloquear classificação automática
- Evidência conflitante com confiança baixa -> escalar para confirmação humana

## Related Documents

- `workflows/wf-detect-operational-mode.yaml` -- Workflow canônico
- `setup-runtime.md` -- Consumidor do contrato operacional
- `operational-test.md` -- Consumidor do contrato operacional
- `wf-create-squad.yaml` -- Pipeline onde esta task é acionada

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
_Sub-tasks: 5 atomic tasks_
