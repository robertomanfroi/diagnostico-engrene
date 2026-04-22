# Task: Create Template — Structure

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-template-structure` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-template-structure
name: "Create Template — Structure"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Define seções, placeholders e recursos especiais do template."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_template_structure
Output: artifact::create_template_structure
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Projetar a estrutura do template com seções, placeholders documentados e regras
de repetição, condicionalidade ou diagrama quando existirem.

## Acceptance Criteria

- [ ] Seções principais definidas
- [ ] Placeholders documentados
- [ ] Recursos especiais explicitados quando aplicáveis

## Related Documents

- `create-template.md`
- `create-template-elicitation.md`

---

_Task Version: 1.0.0_
