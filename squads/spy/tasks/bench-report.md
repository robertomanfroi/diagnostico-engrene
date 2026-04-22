# Task: Executive Report Consolidation (Composed)

## Contrato SINKRA

Domain: `Strategic`

task: benchReport()
responsavel: bench-analyst
atomic_layer: Molecule
Entrada:
- artefatos upstream do benchmark
Saida:
- `executive-report.md`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-report` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: bench-report
name: "Executive Report Consolidation"
category: benchmark-core
agent: bench-analyst
elicit: false
autonomous: true
type: composed
description: "Orquestra carga de evidência, síntese executiva e publicação final do relatório."
```

## Execution Sequence

```text
[1] bench-report-load-evidence        -> carrega e valida artefatos upstream
[2] bench-report-synthesize-findings  -> produz narrativa executiva e recomendações
[3] bench-report-publish              -> grava report final e metadata de rastreio
```

## Sub-Task Reference

| # | Task ID | Responsibility | Output |
|---|---------|----------------|--------|
| 1 | `bench-report-load-evidence` | carregar/validar evidência | evidence bundle |
| 2 | `bench-report-synthesize-findings` | sintetizar narrativa | executive draft |
| 3 | `bench-report-publish` | persistir report final | `executive-report.md` |

## Veto Conditions

- artefatos essenciais ausentes
- números inconsistentes entre matrix/score/gap
- recomendações sem evidência

---

_Task Version: 2.0.0 (atomized stub)_
_Last Updated: 2026-03-27_

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
