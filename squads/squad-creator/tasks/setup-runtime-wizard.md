# Task: Setup Runtime — Guided Wizard

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `setup-runtime-wizard` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: setup-runtime-wizard
name: "Setup Runtime — Guided Wizard"
category: runtime
agent: squad-chief
elicit: true
autonomous: false
description: "Conduz o usuário pela coleta de credenciais e parâmetros de conexão."
accountability:
  human: squad-operator
  scope: full
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::setup_runtime_wizard
Output: artifact::setup_runtime_wizard
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Executar a etapa interativa de coleta de credenciais, URLs, IDs e parâmetros
necessários para cada API configurada.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `runtime_requirements` | object | Yes | Saída de `setup-runtime-requirements` |

## Workflow

### Step 1: Apresentar overview

Mostrar APIs detectadas, prioridade e impacto operacional.

### Step 2: Coletar credenciais por API

Executar o wizard de coleta, respeitando máscara para segredos e permitindo
skip apenas em APIs não críticas.

### Step 3: Consolidar payload

## Output

```yaml
runtime_credentials:
  configured_apis: []
  skipped_apis: []
  captured_variables: []
```

## Acceptance Criteria

- [ ] Overview interativo apresentado
- [ ] Credenciais coletadas para APIs críticas
- [ ] Skips registrados com motivo
- [ ] Payload consolidado emitido

---

_Task Version: 1.0.0_
