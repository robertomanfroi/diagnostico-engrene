# Task: Next Squad Recommendation (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: next-squad
name: "Next Squad Recommendation"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Task composta que orquestra 5 subtasks atômicas para recomendar o próximo squad a criar, melhorar ou corrigir."
owner_workflow: "workflows/wf-next-squad.yaml"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::next_squad
Output: artifact::next_squad
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Responder com uma recomendação priorizada de próximo squad, baseada em registry,
sinais de demanda, scoring explícito e caminho de execução.

## Execution Sequence

```text
INPUT (business_context? + priority_domain? + mode)
    |
[1] next-squad-registry
    -> Lê registry e monta buckets CREATE / IMPROVE / FIX
    |
[2] next-squad-signals
    -> Coleta sinais adicionais de demanda em mode=deep
    |
[3] next-squad-scoring
    -> Aplica as 5 dimensões de score
    |
[4] next-squad-ranking
    -> Ranqueia candidatos e escolhe a ação sugerida
    |
[5] next-squad-report
    -> Emite top 3, quick wins e comando executável
    |
OUTPUT: next_squad_report
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `next-squad-registry` | Scan do ecossistema | Worker |
| 2 | `next-squad-signals` | Sinais de demanda | Hybrid |
| 3 | `next-squad-scoring` | Score composto | Agent |
| 4 | `next-squad-ranking` | Ranking e bucketização | Agent |
| 5 | `next-squad-report` | Relatório final | Agent |

## Commands

```yaml
commands:
  quick: "*next-squad"
  deep: "*next-squad --deep"
  with_context: "*next-squad --context {context}"
  with_domain_bias: "*next-squad --domain {domain}"
  save: "*next-squad --save"
```

## Related Documents

- `workflows/wf-next-squad.yaml`
- `refresh-registry.md`

---

_Task Version: 2.0.0_
