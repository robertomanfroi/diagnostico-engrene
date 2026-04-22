# Task: Improve Workflow Report — Validate and Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-validate-report` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: improve-workflow-report-validate-report
name: "Improve Workflow Report — Validate and Report"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Executa validação pós-edição, rollback quando necessário, aplica version bump e gera o relatório final de melhoria."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_validate_report
Output: artifact::improve_workflow_report_validate_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Fechar o ciclo com validação estrutural, version bump apropriado e diff report
completo, preservando rollback automático em falhas.

## Acceptance Criteria

- [ ] Workflow final parseia em YAML e permanece alcançável
- [ ] Version bump aplicado quando houver mudança real
- [ ] Diff report final gerado com unresolved e tech debt

## Related Documents

- `improve-workflow-from-report.md`
- `workflow-tmpl.yaml`

---

_Task Version: 1.0.0_
