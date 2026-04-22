# Task: Improve Workflow Report — Backup

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-backup` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: improve-workflow-report-backup
name: "Improve Workflow Report — Backup"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Cria e verifica backup antes de qualquer edição, exceto quando o fluxo está em dry-run."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_backup
Output: artifact::improve_workflow_report_backup
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Impor a proteção `backup-first` do processo de melhoria, impedindo edição sem
rollback verificável.

## Acceptance Criteria

- [ ] Backup criado quando `dry_run=false`
- [ ] Backup verificado e caminho registrado
- [ ] Em `dry_run`, a política de não mutação fica explícita

## Related Documents

- `improve-workflow-report-target.md`
- `improve-workflow-report-apply-p1.md`

---

_Task Version: 1.0.0_
