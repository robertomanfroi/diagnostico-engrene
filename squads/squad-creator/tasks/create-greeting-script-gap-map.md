# Task: Create Greeting Script — Gap Map

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script-gap-map` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-greeting-script-gap-map
name: "Create Greeting Script — Gap Map"
category: creation
agent: squad-chief
elicit: false
autonomous: true
description: "Transforma sinais observáveis do squad em tabela signal -> severity -> next_action seguindo a prioridade obrigatória do greeting."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_greeting_script_gap_map
Output: artifact::create_greeting_script_gap_map
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Construir a heurística determinística de `inferNextAction()` sem permitir CTA
genérico quando houver blocker explícito.

## Acceptance Criteria

- [ ] Gap map inclui prioridades `blocking`, `non_blocking` e `intake|ready`
- [ ] Blockers têm precedência explícita
- [ ] Cada sinal produz `next_action` e `reason`

## Related Documents

- `create-greeting-script-discovery.md`
- `create-greeting-script-generate.md`

---

_Task Version: 1.0.0_
