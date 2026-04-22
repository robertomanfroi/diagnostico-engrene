# Task: Deep Research — Publish

## Contrato SINKRA

Domain: `Operational`

task: deepResearchPublish()
responsavel: research-head
atomic_layer: Atom
Entrada:
- memo de síntese
- analysis report
Saida:
- deep dive final + updates de KB/framework
Checklist:
- publicar relatório final
- atualizar framework/KB quando houver novo padrão
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: deep-research-publish
parent_task: deep-research
category: research-atom
agent: research-head
elicit: false
autonomous: true
description: "Publica o deep dive final e registra aprendizados duráveis."
```

## Steps

1. Gerar relatório final em `outputs/spy/reports/deep-dives/`.
2. Garantir links para raw data, transcripts e analysis.
3. Atualizar `knowledge-base.md` e/ou `viral-content-framework.md` se houver padrão novo.
4. Registrar próximos usos do material.

## Acceptance Criteria

- deep dive final salvo
- trilha de evidências preservada
- KB/framework atualizados quando aplicável

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
