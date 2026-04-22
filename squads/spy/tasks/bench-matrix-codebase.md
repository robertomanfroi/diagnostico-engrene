# Task: Bench Matrix — Codebase

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrixCodebase()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `inventory_a`
- `inventory_b`
- `output_dir`
Saida:
- matriz codebase JSON/MD
Checklist:
- mapear agentes, workflows e estrutura
- registrar equivalência e delta específico
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-matrix-codebase
parent_task: bench-matrix
category: benchmark-matrix-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Constrói a matriz estrutural para comparação de codebases."
```

## Steps

1. Carregar inventários A e B.
2. Construir matrix de agentes, workflows e métricas estruturais.
3. Classificar equivalência em `Forte/Parcial/Sem Equivalente`.
4. Persistir `comparison-matrix.json` e `comparison-matrix.md`.

## Acceptance Criteria

- agentes e workflows mapeados
- deltas específicos por linha de comparação
- saída parseável e rastreável

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
