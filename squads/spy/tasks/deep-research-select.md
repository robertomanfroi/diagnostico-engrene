# Task: Deep Research — Selection

## Contrato SINKRA

Domain: `Operational`

task: deepResearchSelect()
responsavel: research-head
atomic_layer: Atom
Entrada:
- catálogo bruto do player
Saida:
- corpus selecionado para análise profunda
Checklist:
- priorizar views, engagement e recência
- fechar corpus mínimo de 10 peças
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: deep-research-select
parent_task: deep-research
category: research-atom
agent: research-head
elicit: false
autonomous: true
description: "Seleciona a amostra final de conteúdo a ser transcrita e analisada."
```

## Steps

1. Ordenar por views, engagement e comentários.
2. Selecionar top 5 por views, top 3 por engagement e 2 recentes.
3. Eliminar duplicatas e conteúdo sem dados mínimos.
4. Persistir corpus escolhido para fases seguintes.

## Acceptance Criteria

- corpus final com 10+ peças
- critério de seleção documentado
- amostra cobre performance + atualidade

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
