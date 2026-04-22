# Task: Create Greeting Script — Discovery

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script-discovery` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-greeting-script-discovery
name: "Create Greeting Script — Discovery"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Resolve config, entry agent, context sources e comandos que alimentam o greeting determinístico."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_greeting_script_discovery
Output: artifact::create_greeting_script_discovery
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Mapear o contrato estrutural do squad para que a geração do greeting dependa apenas
de sinais determinísticos e paths reais.

## Acceptance Criteria

- [ ] `config.yaml` do squad parseado com sucesso
- [ ] `entry_agent` resolvido
- [ ] Context sources e comandos do agente mapeados

## Related Documents

- `create-greeting-script.md`
- `create-greeting-script-gap-map.md`

---

_Task Version: 1.0.0_
