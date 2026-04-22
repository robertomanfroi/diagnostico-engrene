# Task: Bench Gap — Company

## Contrato SINKRA

Domain: `Tactical`

task: benchGapCompany()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- matrix/score company
Saida:
- gap analysis company JSON/MD
Checklist:
- classificar gaps estratégicos e operacionais
- priorizar por ameaça competitiva
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-gap-company
parent_task: bench-gap
category: benchmark-gap-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Deriva gaps bidirecionais para comparações entre empresas."
```

## Steps

1. Ler matriz e score company.
2. Identificar gaps estratégicos, operacionais e de distribuição.
3. Priorizar riscos e oportunidades por ameaça competitiva.
4. Persistir `gap-analysis.json` e `gap-analysis.md`.

## Acceptance Criteria

- riscos competitivos explícitos
- oportunidades priorizadas
- recomendações ancoradas em evidência

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
