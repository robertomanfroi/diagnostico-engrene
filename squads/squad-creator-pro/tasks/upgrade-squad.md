<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: upgrade-squad
  task_name: Upgrade Squad (Composed)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Description'
  - Task output validated against quality standards
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Upgrade Squad (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `upgrade-squad` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: upgrade-squad
name: "Upgrade Squad"
category: upgrade
agent: squad-chief
elicit: true
autonomous: false
description: "Stub composto do pack pro. Reutiliza a base estrutural do squad-creator e adiciona a camada qualitativa e de governança do overlay."
```

## Purpose

Preservar o entrypoint `*upgrade-squad` sem manter o monólito anterior. A base estrutural continua sendo herdada do `squad-creator`; o `pro` adiciona apenas o que é realmente upgrade do pack: leitura de sinais avançados, triagem qualitativa e handoffs de remediação.

## Canonical Owners

- `workflows/wf-upgrade-squad.yaml` é o owner canônico do comando direto `*upgrade-squad`.
- `workflows/wf-brownfield-upgrade-squad.yaml` continua o owner do fluxo brownfield maior e reutiliza este contrato.
- `squads/squad-creator/tasks/upgrade-squad-*.md` seguem como baseline estrutural herdado.

## Command Contract

```text
*upgrade-squad {squad_name}

Flags:
--mode=audit|plan|execute|auto
--focus=agents|tasks|workflows|all
--dry-run
```

## Mode Map

```yaml
mode_map:
  audit:
    run:
      - upgrade-squad-inventory
      - upgrade-squad-gap
  plan:
    run:
      - upgrade-squad-inventory
      - upgrade-squad-gap
      - upgrade-squad-plan
  execute:
    run:
      - upgrade-squad-inventory
      - upgrade-squad-gap
      - upgrade-squad-plan
      - upgrade-squad-qualitative
      - upgrade-squad-apply
      - upgrade-squad-verify
  auto:
    run:
      - upgrade-squad-inventory
      - upgrade-squad-gap
      - upgrade-squad-plan
      - upgrade-squad-qualitative
      - upgrade-squad-apply
      - upgrade-squad-verify
```

## Execution Sequence

| Sequence | Task ID | File | Type |
|----------|---------|------|------|
| 1 | `upgrade-squad-inventory` | `tasks/upgrade-squad-inventory.md` | Worker |
| 2 | `upgrade-squad-gap` | `tasks/upgrade-squad-gap.md` | Agent |
| 3 | `upgrade-squad-plan` | `tasks/upgrade-squad-plan.md` | Hybrid |
| 4 | `upgrade-squad-qualitative` | `tasks/upgrade-squad-qualitative.md` | Agent |
| 5 | `upgrade-squad-apply` | `tasks/upgrade-squad-apply.md` | Hybrid |
| 6 | `upgrade-squad-verify` | `tasks/upgrade-squad-verify.md` | Worker |

## Overlay Rules

- Não duplicar a lógica estrutural já consolidada no `squad-creator`.
- Não inventar conteúdo qualitativo sem evidência no target ou sem handoff explícito.
- Em `auto`, upgrades qualitativos ambíguos viram TODO ou delegação, nunca invenção silenciosa.
- Todo patch estrutural continua sujeito a backup e `dry-run`.

## Outputs

| Output | Description |
|--------|-------------|
| Structural Inventory | Inventário factual com sinais avançados do target |
| Dual-Track Gap Report | Gaps estruturais herdados + gaps qualitativos do pack |
| Upgrade Plan | Plano com trilhas estrutural e qualitativa |
| Upgrade Report | Before/after + TODOs + próximos handoffs |

## Related Documents

- `workflows/wf-upgrade-squad.yaml`
- `workflows/wf-brownfield-upgrade-squad.yaml`
- `squads/squad-creator/tasks/upgrade-squad.md`

_Task Version: 2.0.0_
_Role: compatibility stub for inherited structural upgrade + pro qualitative overlay_

## Acceptance Criteria

- [ ] Output artifact produced: Description
- [ ] Task output validated against quality standards
