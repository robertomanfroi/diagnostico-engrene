# Task: Rename Squad — Structural

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `rename-squad-structural` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: rename-squad-structural
name: "Rename Squad — Structural"
category: maintenance
agent: squad-chief
elicit: false
autonomous: true
description: "Executa branch opcional, git mv do diretório, ajuste interno do squad e rename de scripts locais."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::rename_squad_structural
Output: artifact::rename_squad_structural
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Aplicar a mutação estrutural central do rename sem ainda propagar referências
externas pelo restante do repositório.

## Acceptance Criteria

- [ ] Diretório do squad foi movido corretamente
- [ ] `config.yaml` e arquivos internos refletem `new_name`
- [ ] Scripts internos críticos foram renomeados

## Related Documents

- `rename-squad-map.md`
- `rename-squad-propagate.md`

---

_Task Version: 1.0.0_
