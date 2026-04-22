# Task: Universal Subject Inventory (Composed)

## Contrato SINKRA

Domain: `Tactical`

task: benchInventory()
responsavel: bench-analyst
atomic_layer: Molecule
Entrada:
- `subject_name`
- `comparison_type`
- `data_source_config`
- `output_dir`
Saida:
- inventário JSON/MD do sujeito
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-inventory` |
| **Version** | `3.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: bench-inventory
name: "Universal Subject Inventory"
category: benchmark-core
agent: bench-analyst
elicit: false
autonomous: true
type: composed
description: "Router composto que despacha o inventário para o átomo específico do tipo de comparação."
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

O inventário deixou de ser um pseudo-átomo type-aware gigante. Agora ele atua
como um router fino para um átomo específico por tipo.

## Routing

```text
codebase   -> bench-codebase-recon
llm        -> bench-llm-eval
product    -> bench-product-research
company    -> bench-company-intel
technology -> bench-tech-eval
```

## Sub-Task Reference

| comparison_type | Delegated atom | Output |
|-----------------|----------------|--------|
| `codebase` | `bench-codebase-recon` | inventory codebase |
| `llm` | `bench-llm-eval` | inventory llm |
| `product` | `bench-product-research` | inventory product |
| `company` | `bench-company-intel` | inventory company |
| `technology` | `bench-tech-eval` | inventory technology |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `subject_name` | string | Yes | nome/URL/path do sujeito |
| `comparison_type` | enum | Yes | tipo já resolvido |
| `data_source_config` | object | Yes | estratégia de aquisição |
| `output_dir` | string | Yes | diretório de saída |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Subject Inventory | `{output_dir}/inventory-{subject}.json` | baseline estruturado |
| Subject Inventory MD | `{output_dir}/inventory-{subject}.md` | leitura humana |

## Veto Conditions

- `comparison_type` ausente ou inválido
- átomo delegado inexistente
- inventário final sem dados mínimos do tipo

---

_Task Version: 3.0.0 (atomized stub)_
_Last Updated: 2026-03-27_
