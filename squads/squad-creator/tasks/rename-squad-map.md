# Task: Rename Squad — Map

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `rename-squad-map` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: rename-squad-map
name: "Rename Squad — Map"
category: maintenance
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o blast radius mapping do rename, categoriza superfícies e valida vetoes iniciais."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::rename_squad_map
Output: artifact::rename_squad_map
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Mapear todas as superfícies impactadas antes de qualquer rename estrutural,
bloqueando a operação quando o blast radius não estiver explícito.

## Acceptance Criteria

- [ ] Blast radius gerado e categorizado por zona
- [ ] `old_name` existe e `new_name` não colide
- [ ] Vetoes iniciais avaliados

## Related Documents

- `rename-squad.md`
- `rename-squad-structural.md`

---

_Task Version: 1.0.0_
