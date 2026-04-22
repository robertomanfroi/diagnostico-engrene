# Task: Bench Matrix — Company

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrixCompany()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `inventory_a`
- `inventory_b`
- `output_dir`
Saida:
- matriz company JSON/MD
Checklist:
- comparar posicionamento, execução e moat
- explicitar fontes de evidência
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-matrix-company
parent_task: bench-matrix
category: benchmark-matrix-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Constrói a matriz comparativa para inteligência competitiva de empresas."
```

## Steps

1. Comparar posicionamento, mercado e execução.
2. Avaliar sinais de funding, distribuição e equipe.
3. Consolidar força relativa por dimensão.
4. Persistir matriz final em JSON + MD.

## Acceptance Criteria

- dimensões competitivas cobertas
- vantagens e vulnerabilidades explicitadas
- fontes preservadas no output

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
