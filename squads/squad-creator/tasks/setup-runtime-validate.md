# Task: Setup Runtime — Validate Connections

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `setup-runtime-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: setup-runtime-validate
name: "Setup Runtime — Validate Connections"
category: runtime
agent: squad-chief
elicit: false
autonomous: true
description: "Executa a suíte de validação das conexões configuradas e classifica o resultado."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::setup_runtime_validate
Output: artifact::setup_runtime_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Testar cada conexão configurada com chamadas leves e consolidar o estado real do
runtime antes da persistência.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `runtime_credentials` | object | Yes | Credenciais coletadas |
| `validation_mode` | enum | No | `strict` ou `permissive` |

## Workflow

### Step 1: Rodar validação por API

Executar a chamada de prova, medir latência e registrar detalhes da conta ou do
erro.

### Step 2: Aplicar política de bloqueio

Em `strict`, qualquer API crítica falha bloqueia a continuação.

## Output

```yaml
runtime_validation:
  results: []
  critical_failed: []
  overall_status: "CONNECTED|PARTIAL|FAILED"
```

## Acceptance Criteria

- [ ] Todas as APIs configuradas testadas
- [ ] Latência e detalhes capturados
- [ ] APIs críticas com falha destacadas
- [ ] Status geral emitido

---

_Task Version: 1.0.0_
