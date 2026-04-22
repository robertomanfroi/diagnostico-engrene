# Task: Deep Research — Collection

## Contrato SINKRA

Domain: `Operational`

task: deepResearchCollect()
responsavel: research-head
atomic_layer: Atom
Entrada:
- `handle`
- `platform`
- `depth`
Saida:
- payloads brutos em `outputs/spy/raw/`
Checklist:
- validar acesso às APIs/fallbacks
- coletar 30-50 peças com metadata
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: deep-research-collect
parent_task: deep-research
category: research-atom
agent: research-head
elicit: false
autonomous: true
description: "Coleta dados brutos, metadata e catálogo inicial de conteúdo do player."
```

## Steps

1. Resolver `handle` e `platform`.
2. Coletar catálogo recente e métricas primárias via API/ETL.
3. Persistir payloads brutos em `outputs/spy/raw/{platform}/`.
4. Registrar gaps de dados antes de avançar.

## Acceptance Criteria

- 30+ itens coletados no modo padrão, salvo veto explícito
- views, likes, comments e datas persistidos
- saída bruta versionada por data

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
