# Task: Create Template — Identity

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-template-identity` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-template-identity
name: "Create Template — Identity"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Resolve squad-alvo, identidade do template, formato e modo de uso antes da composição."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_template_identity
Output: artifact::create_template_identity
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Definir a identidade do template, bloquear colisões e produzir o contrato base
que será usado pelas fases seguintes.

## Acceptance Criteria

- [ ] Squad-alvo resolvido e validado
- [ ] `template_id` único dentro do squad
- [ ] Formato e modo de uso explicitados

## Related Documents

- `create-template.md`
- `create-template-structure.md`

---

_Task Version: 1.0.0_
