# Task: Deep Research — Comment Analysis

## Contrato SINKRA

Domain: `Operational`

task: deepResearchComments()
responsavel: research-head
atomic_layer: Atom
Entrada:
- top peças do corpus
Saida:
- mapa de sinais de audiência
Checklist:
- ler comentários relevantes
- classificar elogios, perguntas, pedidos e críticas
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: deep-research-comments
parent_task: deep-research
category: research-atom
agent: research-head
elicit: false
autonomous: true
description: "Extrai verdade da audiência a partir dos comentários do corpus."
```

## Steps

1. Coletar comentários prioritários das peças de maior sinal.
2. Categorizar elogios, dúvidas, pedidos e objeções.
3. Identificar desejos explícitos e gaps percebidos.
4. Persistir audience truth para síntese final.

## Acceptance Criteria

- 50+ comentários úteis analisados quando disponíveis
- categorias de sinal preenchidas
- gaps de audiência explícitos documentados

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
