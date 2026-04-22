# Task: Next Squad — Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `next-squad-report` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: next-squad-report
name: "Next Squad — Report"
category: planning
agent: squad-chief
elicit: false
autonomous: true
description: "Emite o relatório final com top 3, quick wins e trilha de execução sugerida."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::next_squad_report
Output: artifact::next_squad_report
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Entregar uma recomendação acionável e legível, com possibilidade de salvar o
snapshot de scores quando solicitado.

## Acceptance Criteria

- [ ] Top 3 apresentado com rationale
- [ ] Quick wins listados quando existirem
- [ ] Opção de persistir scores suportada

## Related Documents

- `next-squad.md`
- `.aiox/squad-runtime/next-squad/`

---

_Task Version: 1.0.0_
