# Task: Rename Squad — Propagate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `rename-squad-propagate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: rename-squad-propagate
name: "Rename Squad — Propagate"
category: maintenance
agent: squad-chief
elicit: false
autonomous: true
description: "Propaga o novo nome para mirrors IDE, cross-squad refs, workspace, infraestrutura, apps e registries textuais."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::rename_squad_propagate
Output: artifact::rename_squad_propagate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Eliminar referências residuais ao nome antigo fora do diretório do squad
renomeado.

## Acceptance Criteria

- [ ] Mirrors IDE atualizados
- [ ] Refs cross-squad e infra propagadas
- [ ] Nenhuma superfície crítica ficou fora do replace

## Related Documents

- `rename-squad-structural.md`
- `rename-squad-validate.md`

---

_Task Version: 1.0.0_
