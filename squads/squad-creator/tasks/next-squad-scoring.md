# Task: Next Squad — Scoring

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad-scoring` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: next-squad-scoring
name: "Next Squad — Scoring"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica as 5 dimensões de scoring aos candidatos usando evidência do registry e dos sinais coletados."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::next_squad_scoring
Output: artifact::next_squad_scoring
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Pontuar candidatos com uma lógica explícita e comparável, evitando ranking por
impressão.

## Acceptance Criteria

- [ ] 5 dimensões aplicadas aos candidatos elegíveis
- [ ] Fórmula composta explicitada
- [ ] Cada score tem justificativa baseada em evidência

## Related Documents

- `next-squad.md`
- `next-squad-ranking.md`

---

_Task Version: 1.0.0_
