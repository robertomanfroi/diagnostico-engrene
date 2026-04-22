# Task: Next Squad — Ranking

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad-ranking` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: next-squad-ranking
name: "Next Squad — Ranking"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Ordena candidatos, separa buckets de ação e escolhe a trilha de execução recomendada."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::next_squad_ranking
Output: artifact::next_squad_ranking
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar scores em uma fila priorizada de ação com comando executável.

## Acceptance Criteria

- [ ] Candidatos ranqueados por prioridade
- [ ] Buckets CREATE, IMPROVE e FIX preservados
- [ ] Cada top candidate tem comando sugerido

## Related Documents

- `next-squad.md`
- `next-squad-report.md`

---

_Task Version: 1.0.0_
