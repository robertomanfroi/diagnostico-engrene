# Task: Create Greeting Script — Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-greeting-script-validate
name: "Create Greeting Script — Validate"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o script gerado, valida 3 cenários obrigatórios e aplica o checklist de greeting script."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_greeting_script_validate
Output: artifact::create_greeting_script_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Fechar o quality gate do greeting garantindo execução sem erro, presença de
Runtime Directives e priorização correta do Next Action.

## Acceptance Criteria

- [ ] Script executa com exit code `0`
- [ ] 3 cenários obrigatórios foram verificados
- [ ] `checklists/greeting-script-checklist.md` passa

## Related Documents

- `create-greeting-script.md`
- `checklists/greeting-script-checklist.md`

---

_Task Version: 1.0.0_
