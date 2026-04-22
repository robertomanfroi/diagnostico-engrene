# Task: Rename Squad (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `rename-squad` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: rename-squad
name: "Rename Squad"
category: maintenance
agent: squad-chief
elicit: false
autonomous: true
description: "Task composta que formaliza o fluxo shell-first de rename de squad sem alterar o roteamento estável do script."
owner_workflow: "workflows/wf-rename-squad.yaml"
worker_script: "scripts/rename-squad.sh"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::rename_squad
Output: artifact::rename_squad
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Renomear um squad AIOX de forma segura, atualizando todas as superfícies do
repositório e preservando os IDs internos dos agentes.

## Execution Sequence

```text
INPUT (old_name + new_name + optional flags)
    |
[1] rename-squad-map
    -> Mapeia blast radius e vetoes iniciais
    |
[2] rename-squad-structural
    -> Executa git mv, ajuste interno e rename de scripts locais
    |
[3] rename-squad-propagate
    -> Propaga refs para mirrors, cross-squad, infra e apps
    |
[4] rename-squad-validate
    -> Executa grep residual, validate-squad e relatório final
    |
OUTPUT: rename_validation_report
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `rename-squad-map` | Blast radius e vetoes | Worker |
| 2 | `rename-squad-structural` | Rename estrutural do squad | Worker |
| 3 | `rename-squad-propagate` | Propagação repo-wide | Worker |
| 4 | `rename-squad-validate` | Validação final e zero residual | Hybrid |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `old_name` | string | Yes | Nome atual do squad |
| `new_name` | string | Yes | Novo nome do squad |
| `dry_run` | boolean | No | Executa preview sem mutar o repositório |
| `no_branch` | boolean | No | Opera na branch atual |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Squad renomeado | `squads/{new_name}/` | Diretório principal atualizado |
| Validation report | `runtime_context` | Veredito final do rename |
| Residual grep | `runtime_context` | Lista final de refs residuais, se houver |

## Veto Conditions

- Blast radius não executado -> bloquear
- Squad de destino já existe -> bloquear
- Refs residuais > 0 após propagação -> bloquear
- `validate-squad` falha no squad renomeado -> bloquear

## Acceptance Criteria

- [ ] `squads/{old_name}/` não existe mais
- [ ] Refs essenciais usam `new_name`
- [ ] Mirrors IDE atualizados
- [ ] `validate-squad {new_name} --quick` PASS
- [ ] IDs internos dos agentes preservados

## Related Documents

- `workflows/wf-rename-squad.yaml`
- `scripts/rename-squad.sh`
- `refresh-registry.md`

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
