# Task: Create Template — Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-template-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-template-validate
name: "Create Template — Validate"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Compila o arquivo de template e aplica o quality gate SC_TPL_001 antes da gravação final."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_template_validate
Output: artifact::create_template_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que o template compilado é válido, completo e apto para ser gravado no
squad.

## Acceptance Criteria

- [ ] Template compilado sem erro estrutural
- [ ] `SC_TPL_001` avaliado
- [ ] Requisitos bloqueantes aprovados antes do write

## Related Documents

- `create-template.md`
- `create-template-register.md`

---

_Task Version: 1.0.0_
