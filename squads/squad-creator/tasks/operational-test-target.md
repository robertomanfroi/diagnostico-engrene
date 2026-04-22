# Task: Operational Test — Target Selection

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `operational-test-target` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: operational-test-target
name: "Operational Test — Target Selection"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Seleciona o melhor target para o teste operacional com base no modo e no domínio do squad."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::operational_test_target
Output: artifact::operational_test_target
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Escolher o alvo do teste operacional para maximizar cobertura e reduzir risco.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `test_mode` | enum | No | `live` ou `sandbox` |
| `target_id` | string | No | Target explícito |

## Output

```yaml
selected_target:
  type: ""
  id: ""
  name: ""
  details: ""
```

## Acceptance Criteria

- [ ] Target explícito respeitado quando fornecido
- [ ] Seleção automática aplicada quando necessário
- [ ] Evidência do target registrada

---

_Task Version: 1.0.0_
