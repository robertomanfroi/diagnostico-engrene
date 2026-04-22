# Task: Operational Test — Baseline Registration

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `operational-test-baseline` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: operational-test-baseline
name: "Operational Test — Baseline Registration"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Registra o known-good state do teste operacional em operational-baseline.yaml."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::operational_test_baseline
Output: artifact::operational_test_baseline
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Persistir o estado conhecido como operacional para comparação futura.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `selected_target` | object | Yes | Target usado |
| `smoke_results` | object | Yes | Resultado do smoke flow |

## Output

```yaml
operational_baseline:
  file: "squads/{squad_name}/data/operational-baseline.yaml"
  status: "OPERATIONAL|PARTIAL|FAILED"
```

## Acceptance Criteria

- [ ] `operational-baseline.yaml` persistido
- [ ] Target e evidências registrados
- [ ] Status operacional final serializado

---

_Task Version: 1.0.0_
