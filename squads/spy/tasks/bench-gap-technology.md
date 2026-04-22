# Task: Bench Gap — Technology

## Contrato SINKRA

Domain: `Tactical`

task: benchGapTechnology()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- matrix/score technology
Saida:
- gap analysis technology JSON/MD
Checklist:
- classificar gaps de maturidade, DX e ecossistema
- destacar riscos de adoção
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-gap-technology
parent_task: bench-gap
category: benchmark-gap-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Deriva gaps bidirecionais para comparações de tecnologias."
```

## Steps

1. Ler matriz e score technology.
2. Identificar gaps de maturidade, DX, performance e ecossistema.
3. Priorizar por risco de adoção e custo de mudança.
4. Persistir `gap-analysis.json` e `gap-analysis.md`.

## Acceptance Criteria

- riscos técnicos explícitos
- custo de mudança considerado
- roadmap de adoção claro

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
