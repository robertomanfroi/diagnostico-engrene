# Task: Universal Comparison Matrix (Composed)

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrix()
responsavel: bench-analyst
atomic_layer: Molecule
Entrada:
- `inventory_a`
- `inventory_b`
- `comparison_type`
- `output_dir`
Saida:
- `comparison-matrix.json`
- `comparison-matrix.md`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-matrix` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: bench-matrix
name: "Universal Comparison Matrix"
category: benchmark-core
agent: bench-analyst
elicit: false
autonomous: true
type: composed
description: "Router composto que delega a construção da matriz ao átomo específico do tipo."
```

## Routing

```text
codebase   -> bench-matrix-codebase
llm        -> bench-matrix-llm
product    -> bench-matrix-product
company    -> bench-matrix-company
technology -> bench-matrix-technology
```

## Sub-Task Reference

| comparison_type | Delegated atom | Output |
|-----------------|----------------|--------|
| `codebase` | `bench-matrix-codebase` | matriz estrutural |
| `llm` | `bench-matrix-llm` | matriz de specs/capabilities |
| `product` | `bench-matrix-product` | matriz de features/pricing |
| `company` | `bench-matrix-company` | matriz competitiva |
| `technology` | `bench-matrix-technology` | matriz de maturidade/ecossistema |

## Veto Conditions

- inventories incompatíveis entre si
- tipo ausente ou inválido
- átomo delegado não produzir matriz parseável

---

_Task Version: 2.0.0 (atomized stub)_
_Last Updated: 2026-03-27_

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
