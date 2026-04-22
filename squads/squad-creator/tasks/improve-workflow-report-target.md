# Task: Improve Workflow Report — Target

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-target` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: improve-workflow-report-target
name: "Improve Workflow Report — Target"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Valida o workflow alvo citado no report, checa existência, parse YAML e reconcilia id/versão."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_target
Output: artifact::improve_workflow_report_target
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que a remediação está apontando para um workflow real e compatível com o
report antes de qualquer mutação.

## Acceptance Criteria

- [ ] Workflow alvo existe e parseia em YAML
- [ ] `workflow.id` reconciliado com o report
- [ ] Divergência de versão registrada quando houver

## Related Documents

- `improve-workflow-report-ingest.md`
- `improve-workflow-report-backup.md`

---

_Task Version: 1.0.0_
