# Task: Deep Research — Pattern Analysis

## Contrato SINKRA

Domain: `Operational`

task: deepResearchPatterns()
responsavel: research-head
atomic_layer: Atom
Entrada:
- corpus selecionado
- transcrições anotadas
Saida:
- análise de padrões em `outputs/spy/analysis/players/`
Checklist:
- mapear títulos, hooks, estrutura e linguagem
- validar padrões com recorrência mínima
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: deep-research-patterns
parent_task: deep-research
category: research-atom
agent: research-head
elicit: false
autonomous: true
description: "Transforma corpus + transcrições em padrões replicáveis de conteúdo."
```

## Steps

1. Classificar fórmulas de títulos.
2. Mapear hooks, estrutura e ritmo.
3. Identificar linguagem, catchphrases e promessas recorrentes.
4. Persistir relatório de padrões replicáveis.

## Acceptance Criteria

- 3+ padrões validados com evidência
- análise cobre títulos, hooks, estrutura e linguagem
- saídas salvas em `outputs/spy/analysis/players/`

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
