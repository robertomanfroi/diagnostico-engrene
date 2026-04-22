# Task: Bench Matrix — Product

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrixProduct()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `inventory_a`
- `inventory_b`
- `output_dir`
Saida:
- matriz product JSON/MD
Checklist:
- comparar features, UX, pricing e integrações
- registrar tradeoffs explícitos
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-matrix-product
parent_task: bench-matrix
category: benchmark-matrix-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Constrói a matriz comparativa para produtos de software."
```

## Steps

1. Mapear features equivalentes e gaps.
2. Comparar pricing, UX e integrações.
3. Registrar deltas acionáveis por categoria.
4. Persistir matriz final em JSON + MD.

## Acceptance Criteria

- features e pricing comparados
- deltas específicos, não genéricos
- matriz útil para decisão de produto

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
