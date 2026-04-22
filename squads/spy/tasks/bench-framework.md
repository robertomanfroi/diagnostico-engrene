# Task: Full Framework Benchmark (Composed)

## Contrato SINKRA

Domain: `Tactical`

task: benchFramework()
responsavel: bench-analyst
atomic_layer: Molecule
Entrada:
- `subject_a`
- `subject_b`
- `comparison_type`
- `profile`
Saida:
- benchmark packet em `docs/bench/{subject_a}-vs-{subject_b}/`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-framework` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: bench-framework
name: "Full Framework Benchmark"
category: benchmark
agent: bench-analyst
elicit: true
autonomous: false
type: composed
workflow: bench-comparison-pipeline
description: "Stub composto que preserva o comando público *bench e delega a execução para detect, inventory, matrix, score, gap, deep dive, report e battle card."
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Preserva o entrypoint público do benchmark completo, mas remove a falsa atomização.
O comportamento canônico agora é delegar para o workflow
[`bench-comparison-pipeline.yaml`](../workflows/bench-comparison-pipeline.yaml)
e para tasks especializadas já atomizadas ou reatomizadas.

## Execution Sequence

```text
[0] bench-detect
[1] bench-inventory (subject_a)
[2] bench-inventory (subject_b)
[3] bench-matrix
[4] bench-score
[5] bench-gap
[6] deep dive por tipo (bench-deep-compare / bench-hooks / bench-absorb / bench-migrate / bench-llm-eval / bench-product-research / bench-company-intel / bench-tech-eval)
[7] bench-report
[8] bench-battle-card
[9] bench-quality-checklist
```

## Routing Rules

- `profile=quick` pode encerrar em `bench-battle-card`
- `profile=standard` executa até `bench-report`
- `profile=full` executa todas as fases e checklist final
- `comparison_type=auto` exige `bench-detect` antes de qualquer roteamento

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `subject_a` | string | Yes | primeiro sujeito |
| `subject_b` | string | Yes | segundo sujeito |
| `comparison_type` | enum | No | `auto`, `codebase`, `llm`, `product`, `company`, `technology` |
| `profile` | enum | No | `quick`, `standard`, `full` |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Benchmark Directory | `docs/bench/{subject_a}-vs-{subject_b}/` | artefatos consolidados |
| Executive Report | `docs/bench/{subject_a}-vs-{subject_b}/executive-report.md` | visão executiva |
| Battle Card | `docs/bench/{subject_a}-vs-{subject_b}/battle-card.md` | decisão rápida |

## Veto Conditions

- Benchmark contra o mesmo sujeito
- `codebase` sem fonte local ou repo utilizável
- Inventário vazio em qualquer sujeito
- Tipo não detectado nem explicitado

---

_Task Version: 2.0.0 (atomized stub)_
_Last Updated: 2026-03-27_
