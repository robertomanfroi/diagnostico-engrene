# Task: Improve Workflow from Gap Report (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `improve-workflow-from-report` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: improve-workflow-from-report
name: "Improve Workflow from Gap Report"
category: improvement
agent: squad-chief
elicit: false
autonomous: true
description: "Task composta que consome um gap report de workflow, aplica remediações P1/P2 rastreáveis e gera diff report com rollback seguro."
owner_workflow: "workflows/wf-improve-workflow-from-report.yaml"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::improve_workflow_from_report
Output: artifact::improve_workflow_from_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Aplicar melhorias de qualidade em um workflow YAML existente com base em um gap
report estruturado, mantendo a regra `backup-first`, sem inventar correções fora
do contrato do relatório.

## Execution Sequence

```text
INPUT (gap_report_path + dry_run + priority_filter)
    |
[1] improve-workflow-report-ingest
    -> Parseia gap report e extrai contrato de remediação
    |
[2] improve-workflow-report-target
    -> Valida workflow alvo, id e versão
    |
[3] improve-workflow-report-backup
    -> Cria backup verificável antes de qualquer mutação
    |
[4] improve-workflow-report-apply-p1
    -> Aplica remediações críticas e registra diff log
    |
[5] improve-workflow-report-apply-secondary
    -> Aplica P2 e converte P3 em tech debt
    |
[6] improve-workflow-report-validate-report
    -> Valida o workflow final, aplica version bump e gera relatório
    |
OUTPUT: workflow_improvement_report
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `improve-workflow-report-ingest` | Ingerir e validar gap report | Worker |
| 2 | `improve-workflow-report-target` | Validar workflow alvo | Worker |
| 3 | `improve-workflow-report-backup` | Garantir backup antes de mutação | Worker |
| 4 | `improve-workflow-report-apply-p1` | Aplicar remediações críticas | Agent |
| 5 | `improve-workflow-report-apply-secondary` | Tratar P2 e P3 | Hybrid |
| 6 | `improve-workflow-report-validate-report` | Validar, versionar e reportar | Worker |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `gap_report_path` | filepath | Yes | Caminho do YAML produzido por `analyze-workflow` |
| `dry_run` | boolean | No | Se `true`, não muta o workflow e gera apenas o diff report |
| `priority_filter` | enum | No | `all`, `p1_only` ou `p1_p2` |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Workflow melhorado | `{target_workflow_file}` | Workflow atualizado in-place |
| Diff report | `outputs/squad-creator/workflow-improvements/{workflow-name}-diff.md` | Registro completo das mudanças |
| Backup | `{target_workflow_file}.bak.{timestamp}` | Rollback seguro |

## Veto Conditions

- Gap report inválido ou fora do schema esperado -> bloquear
- Workflow alvo inexistente -> bloquear
- Falha ao criar backup -> bloquear
- Workflow final inválido após edição -> rollback e bloquear
- Mudança não rastreável ao gap report -> bloquear

## Acceptance Criteria

- [ ] Gap report parseado com sucesso
- [ ] Workflow alvo reconciliado com o report
- [ ] Backup criado antes de editar quando `dry_run=false`
- [ ] Remediações P1 tratadas
- [ ] P2/P3 respeitam `priority_filter`
- [ ] Workflow final validado com diff report completo

## Related Documents

- `workflows/wf-improve-workflow-from-report.yaml`
- `workflow-tmpl.yaml`
- `analyze-workflow.md`

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
