# Task: Operational Test — Report and Decision

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `operational-test-report` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: operational-test-report
name: "Operational Test — Report and Decision"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Apresenta o resultado do teste operacional e o veredito de readiness."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::operational_test_report
Output: artifact::operational_test_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar a execução operacional em decisão clara: pronto para produção,
parcialmente operacional ou bloqueado.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `selected_target` | object | Yes | Target do teste |
| `smoke_results` | object | Yes | Resultado do fluxo |
| `operational_baseline` | object | Yes | Baseline persistido |

## Output

```yaml
operational_report:
  ready_for_production: false
  decision: "OPERATIONAL|PARTIAL|FAILED"
  recommended_next_step: ""
```

## Acceptance Criteria

- [ ] Resultado apresentado de forma legível
- [ ] Veredito operacional emitido
- [ ] Próximo passo recomendado

---

_Task Version: 1.0.0_
