# Task: Create Template — Register

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-template-register` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-template-register
name: "Create Template — Register"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Grava o template final, atualiza README quando necessário e registra a criação."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_template_register
Output: artifact::create_template_register
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Persistir o template e deixar o squad com o inventário de templates atualizado.

## Acceptance Criteria

- [ ] Arquivo gravado em `templates/`
- [ ] README ou índice local atualizado quando aplicável
- [ ] Registro final da criação emitido

## Related Documents

- `create-template.md`
- `templates/`

---

_Task Version: 1.0.0_
