# Task: Bench Gap — Product

## Contrato SINKRA

Domain: `Tactical`

task: benchGapProduct()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- matrix/score product
Saida:
- gap analysis product JSON/MD
Checklist:
- classificar gaps de feature, UX e pricing
- registrar quick wins e structural gaps
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-gap-product
parent_task: bench-gap
category: benchmark-gap-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Deriva gaps bidirecionais para comparações de produto."
```

## Steps

1. Ler matriz e score do produto.
2. Identificar gaps de feature set, experiência e monetização.
3. Separar quick wins de mudanças estruturais.
4. Persistir `gap-analysis.json` e `gap-analysis.md`.

## Acceptance Criteria

- gaps categorizados por tipo
- quick wins destacados
- backlog de absorção claro

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
