# Task: Detect Operational Mode — Infrastructure Plan

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `detect-operational-mode-infrastructure` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: detect-operational-mode-infrastructure
name: "Detect Operational Mode — Infrastructure Plan"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Traduz o modo detectado em plano de APIs, variáveis de ambiente e ativos operacionais."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::detect_operational_mode_infrastructure
Output: artifact::detect_operational_mode_infrastructure
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Quando o squad for operacional, produzir um plano de infraestrutura que o
restante do pipeline possa usar para setup, validação E2E e geração de tasks
operacionais. Em modo textual, emitir um plano nulo explícito.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `mode_report` | object | Yes | Saída de `detect-operational-mode-classify` |
| `squad_name` | string | No | Nome do squad alvo |

## Workflow

### Step 1: Se textual, emitir plano nulo

Retornar que nenhuma conexão externa é obrigatória e que o fluxo segue apenas
com QA estrutural.

### Step 2: Se operacional, mapear infraestrutura

Transformar os sistemas detectados em:

- `required_apis`
- `env_vars_template`
- `setup_instructions`
- `operational_assets`

### Step 3: Emitir plano final

Produzir contrato consumível por `setup-runtime`, `operational-test` e
`wf-create-squad`.

## Output

```yaml
infrastructure_plan:
  mode_detected: "OPERATIONAL|TEXTUAL"
  required_apis: []
  env_vars_template: []
  operational_assets:
    - "setup-runtime.md"
    - "operational-test.md"
    - "auto-heal.md"
  next_phase: "phase_7 if operational else phase_5"
```

## Acceptance Criteria

- [ ] Plano textual nulo emitido quando aplicável
- [ ] APIs requeridas explicitadas quando modo = OPERATIONAL
- [ ] Próximas tasks operacionais declaradas
- [ ] Contrato final consumível por `wf-create-squad`

## Related Documents

- `detect-operational-mode.md` -- Task composta
- `setup-runtime.md` -- Consumidor do contrato operacional
- `operational-test.md` -- Consumidor do contrato operacional

---

_Task Version: 1.0.0_
