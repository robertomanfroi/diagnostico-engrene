# Task: Sync Chief Codex Skill

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `sync-chief-codex-skill` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: sync-chief-codex-skill
name: "Sync Chief Codex Skill"
category: utility
agent: squad-chief
elicit: false
autonomous: true
description: "Gera ou atualiza .codex/skills/{chief_id}/SKILL.md a partir do chief do squad."
worker_script: "scripts/sync-chief-codex-skill.js"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::sync_chief_codex_skill
Output: artifact::sync_chief_codex_skill
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que o chief do squad fique imediatamente ativável no Codex após a
publicação do squad ou após mudanças no entry agent.

## Deterministic Execution

```bash
node squads/squad-creator/scripts/sync-chief-codex-skill.js --squad {squad_name}
```

## Acceptance Criteria

- [ ] `config.yaml` do squad parseia sem erro
- [ ] Chief resolvido a partir de `entry_agent` ou fallback canônico
- [ ] `.codex/skills/{chief_id}/SKILL.md` gerado
- [ ] Skill aponta para o agent file real do chief

## Veto Conditions

- `config.yaml` ausente ou inválido
- Chief não resolvido
- Agent file do chief ausente

## Related Documents

- `create-squad-publish.md`
- `scripts/sync-chief-codex-skill.js`

---

_Task Version: 1.0.0_
