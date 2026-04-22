# Task: Improve Workflow Report — Ingest

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-ingest` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: improve-workflow-report-ingest
name: "Improve Workflow Report — Ingest"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Lê o gap report, valida o contrato mínimo e extrai workflow, versão, score e remediações."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_ingest
Output: artifact::improve_workflow_report_ingest
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar o gap report em um contrato de entrada confiável para as fases
seguintes, sem inferir nada além do que o relatório declara.

## Acceptance Criteria

- [ ] Gap report parseado como YAML válido
- [ ] `workflow_analyzed` e `workflow_version` extraídos
- [ ] Pelo menos um gap ou remediation item presente

## Related Documents

- `improve-workflow-from-report.md`
- `improve-workflow-report-target.md`

---

_Task Version: 1.0.0_
