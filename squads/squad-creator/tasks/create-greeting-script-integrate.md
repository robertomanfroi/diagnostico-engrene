# Task: Create Greeting Script — Integrate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script-integrate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-greeting-script-integrate
name: "Create Greeting Script — Integrate"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Persiste o script gerado, atualiza STEP 3.5 do entry agent e registra o script no config do squad."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_greeting_script_integrate
Output: artifact::create_greeting_script_integrate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Conectar o artefato gerado ao ciclo real de ativação do squad sem quebrar o
agent de entrada nem o inventário de scripts.

## Acceptance Criteria

- [ ] Script salvo em `scripts/generate-{squad}-greeting.cjs`
- [ ] Entry agent atualizado com STEP 3.5
- [ ] `config.yaml` do squad registra o script

## Related Documents

- `create-greeting-script-generate.md`
- `create-greeting-script-validate.md`

---

_Task Version: 1.0.0_
