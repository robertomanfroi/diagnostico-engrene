# Task: Create Template — Elicitation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-template-elicitation` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-template-elicitation
name: "Create Template — Elicitation"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Configura o fluxo de elicitação quando o template é interativo, ou emite skip explícito quando ele é automático."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_template_elicitation
Output: artifact::create_template_elicitation
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Serializar a experiência de elicitação do template e evitar que a interatividade
fique implícita ou incompleta.

## Acceptance Criteria

- [ ] Templates interativos têm fluxo configurado
- [ ] Templates automáticos produzem `skip_reason` explícito
- [ ] Opções e seções de elicitação ficaram claras

## Related Documents

- `create-template.md`
- `create-template-validate.md`

---

_Task Version: 1.0.0_
