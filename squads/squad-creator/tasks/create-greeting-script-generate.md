# Task: Create Greeting Script — Generate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script-generate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-greeting-script-generate
name: "Create Greeting Script — Generate"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Preenche o template greeting-script-tmpl.cjs com context sources, gap map, seções do greeting e directives de runtime."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_greeting_script_generate
Output: artifact::create_greeting_script_generate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Renderizar um script `.cjs` completo a partir do template canônico, preservando
as funções `collectContext`, `inferNextAction`, `buildGreeting` e
`buildDirectives`.

## Acceptance Criteria

- [ ] `templates/greeting-script-tmpl.cjs` foi usado como base
- [ ] Placeholders obrigatórios foram preenchidos
- [ ] Output inclui Next Action e Runtime Directives

## Related Documents

- `templates/greeting-script-tmpl.cjs`
- `create-greeting-script-integrate.md`

---

_Task Version: 1.0.0_
