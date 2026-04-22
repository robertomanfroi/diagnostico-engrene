# Task: Next Squad — Registry Scan

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad-registry` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: next-squad-registry
name: "Next Squad — Registry Scan"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Lê o registry do ecossistema e produz os buckets CREATE, IMPROVE e FIX."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::next_squad_registry
Output: artifact::next_squad_registry
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Estabelecer a visão factual do ecossistema antes de pontuar prioridades.

## Acceptance Criteria

- [ ] Registry carregado ou bloqueio explícito emitido
- [ ] Buckets CREATE, IMPROVE e FIX produzidos
- [ ] Cobertura de domínio resumida

## Related Documents

- `next-squad.md`
- `next-squad-signals.md`

---

_Task Version: 1.0.0_
