# Task: Deep Player Research (Composed)

## Contrato SINKRA

Domain: `Operational`

task: deepResearch()
responsavel: research-head
atomic_layer: Molecule
Entrada:
- `handle`
- `platform`
- `depth`
Saida:
- research packet em `outputs/spy/`
Checklist:
- `checklists/content-creation-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `deep-research` |
| **Version** | `3.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `research-head` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: deep-research
name: "Deep Player Research"
category: research
agent: research-head
elicit: true
autonomous: false
type: composed
description: "Orquestra 7 átomos para coleta, seleção, transcrição, análise de padrões, análise de comentários, síntese e publicação do deep dive."
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Preserva o comando público `deep-research` sem manter um monólito operacional.
Cada fase do deep dive agora vive em um átomo independente, com responsabilidade
única e artefatos verificáveis.

## Execution Sequence

```text
[1] deep-research-collect    -> coleta dados brutos e metadata
[2] deep-research-select     -> seleciona amostra de conteúdo
[3] deep-research-transcribe -> extrai/anota transcrições
[4] deep-research-patterns   -> identifica padrões replicáveis
[5] deep-research-comments   -> lê sinais da audiência
[6] deep-research-synthesis  -> consolida Content DNA + aplicações
[7] deep-research-publish    -> publica deep dive e atualiza KB/framework
```

## Sub-Task Reference

| # | Task ID | Fase | Output principal |
|---|---------|------|------------------|
| 1 | `deep-research-collect` | Collection | raw payloads |
| 2 | `deep-research-select` | Selection | corpus selecionado |
| 3 | `deep-research-transcribe` | Transcription | transcripts anotados |
| 4 | `deep-research-patterns` | Pattern Analysis | analysis report |
| 5 | `deep-research-comments` | Comment Analysis | audience signals |
| 6 | `deep-research-synthesis` | Synthesis | synthesis memo |
| 7 | `deep-research-publish` | Publication | deep-dive final |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `handle` | string | Yes | Canal/perfil alvo |
| `platform` | enum | Yes | `youtube` ou `instagram` |
| `depth` | enum | No | `standard` ou `comprehensive` |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Raw Data | `outputs/spy/raw/{platform}/` | respostas de API/ETL |
| Transcripts | `outputs/spy/transcripts/{platform}/` | transcrições anotadas |
| Analysis | `outputs/spy/analysis/players/` | análise de padrões |
| Deep Dive | `outputs/spy/reports/deep-dives/` | relatório final |

## Veto Conditions

- Sem acesso a fonte primária de dados
- Menos de 10 peças públicas úteis no modo `standard`
- Transcrições indisponíveis sem fallback viável
- Padrões sem evidência mínima de recorrência

## Error Handling

```yaml
error_handling:
  sub_task_failure:
    - interromper no átomo com falha
    - registrar contexto e artefato faltante
    - permitir retry isolado do átomo
  resume:
    - retomar a partir do último átomo concluído
```

---

_Task Version: 3.0.0 (atomized stub)_
_Last Updated: 2026-03-27_
