# Task: Improve Workflow Report — Apply P1

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-apply-p1` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: improve-workflow-report-apply-p1
name: "Improve Workflow Report — Apply P1"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica remediações P1 rastreáveis ao report e registra diff log de cada mudança crítica."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_apply_p1
Output: artifact::improve_workflow_report_apply_p1
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Executar as correções obrigatórias sem inventar melhoria fora do contrato do gap
report.

## Acceptance Criteria

- [ ] Todas as remediações P1 foram aplicadas ou marcadas como unresolved
- [ ] Cada mudança registra antes/depois e `gap_ref`
- [ ] Nenhuma fix extrapola o conteúdo do report

## Related Documents

- `improve-workflow-report-backup.md`
- `improve-workflow-report-apply-secondary.md`

---

_Task Version: 1.0.0_
