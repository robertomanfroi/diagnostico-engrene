# Task: Setup Runtime — Load Requirements

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `setup-runtime-requirements` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: setup-runtime-requirements
name: "Setup Runtime — Load Requirements"
category: runtime
agent: squad-chief
elicit: false
autonomous: true
description: "Carrega api-requirements.yaml e classifica APIs por prioridade."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::setup_runtime_requirements
Output: artifact::setup_runtime_requirements
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Normalizar o contrato de APIs exigidas pelo squad operacional antes de abrir o
wizard de credenciais.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `required_apis` | list | No | Lista já derivada pelo fluxo anterior |

## Workflow

### Step 1: Carregar `api-requirements.yaml`

Ler `squads/{squad_name}/data/api-requirements.yaml` quando existir. Se a lista
já vier em input, usar como fonte primária e validar consistência.

### Step 2: Classificar prioridades

Separar `critical`, `recommended` e `optional`.

### Step 3: Emitir pacote normalizado

## Output

```yaml
runtime_requirements:
  required_apis: []
  critical_apis: []
  recommended_apis: []
  optional_apis: []
```

## Acceptance Criteria

- [ ] Fonte de requisitos carregada
- [ ] APIs categorizadas por prioridade
- [ ] Pacote normalizado emitido

---

_Task Version: 1.0.0_
