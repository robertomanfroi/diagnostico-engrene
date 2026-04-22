# Task: Bench Matrix — Technology

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrixTechnology()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `inventory_a`
- `inventory_b`
- `output_dir`
Saida:
- matriz technology JSON/MD
Checklist:
- comparar maturidade, DX, performance e ecossistema
- diferenciar fato de opinião
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-matrix-technology
parent_task: bench-matrix
category: benchmark-matrix-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Constrói a matriz comparativa para tecnologias e frameworks."
```

## Steps

1. Comparar maturidade e adoção.
2. Comparar DX, performance e ecossistema.
3. Sinalizar tradeoffs reais por dimensão.
4. Persistir matriz final em JSON + MD.

## Acceptance Criteria

- maturidade, DX e performance cobertos
- tradeoffs explícitos
- output rastreável para fontes técnicas

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
