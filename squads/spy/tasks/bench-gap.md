# Task: Universal Bidirectional Gap Analysis (Composed)

## Contrato SINKRA

Domain: `Tactical`

task: benchGap()
responsavel: bench-analyst
atomic_layer: Molecule
Entrada:
- `subject_a`
- `subject_b`
- `comparison_type`
- evidências de matrix/score
Saida:
- `gap-analysis.json`
- `gap-analysis.md`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-gap` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: bench-gap
name: "Universal Gap Analysis"
category: benchmark-core
agent: bench-analyst
elicit: false
autonomous: true
type: composed
description: "Router composto que delega o gap analysis ao átomo específico por tipo, preservando compatibilidade com o legado codebase."
```

## Routing

```text
codebase   -> bench-gap-analysis
llm        -> bench-gap-llm
product    -> bench-gap-product
company    -> bench-gap-company
technology -> bench-gap-technology
```

## Sub-Task Reference

| comparison_type | Delegated atom | Output |
|-----------------|----------------|--------|
| `codebase` | `bench-gap-analysis` | roadmap de absorção legado |
| `llm` | `bench-gap-llm` | gaps de capability/cost |
| `product` | `bench-gap-product` | gaps de feature/UX/pricing |
| `company` | `bench-gap-company` | gaps competitivos/execução |
| `technology` | `bench-gap-technology` | gaps de maturidade/DX/ecossistema |

## Veto Conditions

- matriz ausente
- score ausente quando exigido
- gap sem evidência rastreável

---

_Task Version: 2.0.0 (atomized stub)_
_Last Updated: 2026-03-27_

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
