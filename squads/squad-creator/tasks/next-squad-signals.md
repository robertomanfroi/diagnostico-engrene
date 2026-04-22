# Task: Next Squad — Signals

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad-signals` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: next-squad-signals
name: "Next Squad — Signals"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Coleta sinais adicionais de demanda em modo deep ou emite skip explícito em modo quick."
accountability:
  human: squad-operator
  scope: full
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::next_squad_signals
Output: artifact::next_squad_signals
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Adicionar contexto de demanda real sem acoplar o fluxo rápido a scans pesados.

## Acceptance Criteria

- [ ] Modo `quick` produz skip explícito
- [ ] Modo `deep` coleta sinais de workspace, git e runtime
- [ ] Evidências ficam separadas do scoring

## Related Documents

- `next-squad.md`
- `next-squad-scoring.md`

---

_Task Version: 1.0.0_
