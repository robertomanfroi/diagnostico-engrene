# Task: Bench Gap — LLM

## Contrato SINKRA

Domain: `Tactical`

task: benchGapLLM()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- matrix/score llm
Saida:
- gap analysis llm JSON/MD
Checklist:
- classificar gaps por capability, cost e positioning
- gerar recomendações priorizadas
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-gap-llm
parent_task: bench-gap
category: benchmark-gap-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Deriva gaps bidirecionais para comparações de LLM."
```

## Steps

1. Ler matriz e score do benchmark.
2. Identificar gaps de capability, custo e posicionamento.
3. Priorizar por impacto e reversibilidade.
4. Persistir `gap-analysis.json` e `gap-analysis.md`.

## Acceptance Criteria

- gaps rastreáveis a evidência
- prioridades justificadas
- recomendações acionáveis

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
