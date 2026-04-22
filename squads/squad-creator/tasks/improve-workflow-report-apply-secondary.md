# Task: Improve Workflow Report — Apply Secondary

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-report-apply-secondary` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: improve-workflow-report-apply-secondary
name: "Improve Workflow Report — Apply Secondary"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica P2 quando permitido pelo filtro e converte P3 em tech debt explícita para o diff report."
accountability:
  human: squad-operator
  scope: full
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::improve_workflow_report_apply_secondary
Output: artifact::improve_workflow_report_apply_secondary
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Separar o que deve ser aplicado agora do que precisa virar backlog técnico,
mantendo o ciclo conservador de melhoria.

## Acceptance Criteria

- [ ] P2 respeita `priority_filter`
- [ ] P2 complexos demais viram nota explícita
- [ ] P3 documentados como tech debt

## Related Documents

- `improve-workflow-report-apply-p1.md`
- `improve-workflow-report-validate-report.md`

---

_Task Version: 1.0.0_
