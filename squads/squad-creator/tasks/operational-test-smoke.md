# Task: Operational Test — Smoke Flow

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `operational-test-smoke` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: operational-test-smoke
name: "Operational Test — Smoke Flow"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o smoke workflow operacional mínimo: fetch, process, output e notificação quando aplicável."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::operational_test_smoke
Output: artifact::operational_test_smoke
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Executar o fluxo E2E mínimo do squad com dados reais ou de sandbox e produzir os
artefatos básicos de prova.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `selected_target` | object | Yes | Target selecionado |
| `test_mode` | enum | No | `live` ou `sandbox` |
| `test_scope` | enum | No | `minimal`, `standard` ou `full` |

## Output

```yaml
smoke_results:
  tests_passed: "0/0"
  artifacts_generated: []
  overall_status: "OPERATIONAL|PARTIAL|FAILED"
```

## Acceptance Criteria

- [ ] Fluxo mínimo executado
- [ ] Artefatos de prova gerados
- [ ] Resultado consolidado emitido

---

_Task Version: 1.0.0_
