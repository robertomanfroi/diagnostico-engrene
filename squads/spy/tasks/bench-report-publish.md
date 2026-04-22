# Task: Bench Report — Publish

## Contrato SINKRA

Domain: `Strategic`

task: benchReportPublish()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- executive draft
- evidence bundle
Saida:
- `executive-report.md`
Checklist:
- publicar arquivo final
- preservar trilha de rastreabilidade
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-report-publish
parent_task: bench-report
category: benchmark-report-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Publica o relatório executivo final com rastreabilidade preservada."
```

## Steps

1. Renderizar `executive-report.md`.
2. Inserir metadata mínima de método, fontes e confiança.
3. Garantir links para artefatos upstream.
4. Salvar report final no diretório do benchmark.

## Acceptance Criteria

- report final salvo
- método e fontes explícitos
- trilha de evidência preservada

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
