# Task: Operational Test — Preflight

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `operational-test-preflight` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: operational-test-preflight
name: "Operational Test — Preflight"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Valida baseline de runtime, conexões críticas e pré-condições do teste operacional."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::operational_test_preflight
Output: artifact::operational_test_preflight
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que o squad está elegível para um teste operacional real antes de
executar smoke flow ou gerar artefatos.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `target_id` | string | No | Target explícito |

## Output

```yaml
operational_preflight:
  baseline_exists: true
  critical_connections_valid: true
  target_ready: true
```

## Acceptance Criteria

- [ ] `runtime-baseline.yaml` validado
- [ ] APIs críticas verificadas
- [ ] Target elegível confirmado

---

_Task Version: 1.0.0_
