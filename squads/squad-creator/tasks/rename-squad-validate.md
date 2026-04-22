# Task: Rename Squad — Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `rename-squad-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: rename-squad-validate
name: "Rename Squad — Validate"
category: maintenance
agent: squad-chief
elicit: false
autonomous: true
description: "Executa grep residual, roda validate-squad no alvo renomeado e emite o relatório final do rename."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::rename_squad_validate
Output: artifact::rename_squad_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Fechar o rename com verificação objetiva de resíduos, saúde estrutural e
preservação dos agent IDs internos.

## Acceptance Criteria

- [ ] Grep residual retorna zero refs relevantes
- [ ] `validate-squad {new_name} --quick` passa
- [ ] Relatório final do rename foi emitido

## Related Documents

- `rename-squad.md`
- `scripts/rename-squad.sh`

---

_Task Version: 1.0.0_
