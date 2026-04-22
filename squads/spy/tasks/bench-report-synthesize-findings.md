# Task: Bench Report — Synthesize Findings

## Contrato SINKRA

Domain: `Strategic`

task: benchReportSynthesizeFindings()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- evidence bundle
Saida:
- executive draft
Checklist:
- resumir winner/loser por dimensão
- transformar evidência em recomendação executiva
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-report-synthesize-findings
parent_task: bench-report
category: benchmark-report-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Transforma o evidence bundle em narrativa executiva e recomendações."
```

## Steps

1. Resumir resultado por dimensão.
2. Consolidar principais gaps e diferenciais.
3. Gerar recomendações executivas priorizadas.
4. Produzir draft narrativo do report.

## Acceptance Criteria

- narrativa executiva clara
- recomendações priorizadas
- cada claim aponta para evidência específica

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
