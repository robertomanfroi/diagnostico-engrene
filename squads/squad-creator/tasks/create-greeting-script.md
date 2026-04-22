# Task: Create Greeting Script (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-greeting-script` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: create-greeting-script
name: "Create Greeting Script"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Task composta que orquestra 5 subtasks atômicas para gerar greeting scripts determinísticos com Next Action."
owner_workflow: "workflows/wf-create-greeting-script.yaml"
pattern: "GREETING-CONTINUITY-001"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_greeting_script
Output: artifact::create_greeting_script
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Gerar um `generate-{squad}-greeting.cjs` completo para qualquer squad, usando o
template canônico, um gap map determinístico e integração obrigatória com o
entry agent via STEP 3.5.

## Execution Sequence

```text
INPUT (squad_name + optional entry_agent)
    |
[1] create-greeting-script-discovery
    -> Resolve config, context sources e comandos do entry agent
    |
[2] create-greeting-script-gap-map
    -> Constrói signal -> severity -> next_action
    |
[3] create-greeting-script-generate
    -> Preenche greeting-script-tmpl.cjs e renderiza o script
    |
[4] create-greeting-script-integrate
    -> Salva o .cjs, atualiza STEP 3.5 e registra no config
    |
[5] create-greeting-script-validate
    -> Executa, testa 3 cenários e aplica o checklist
    |
OUTPUT: greeting_validation_report
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `create-greeting-script-discovery` | Descobrir config, context sources e comandos | Hybrid |
| 2 | `create-greeting-script-gap-map` | Definir heurística determinística de Next Action | Agent |
| 3 | `create-greeting-script-generate` | Preencher template e gerar script | Hybrid |
| 4 | `create-greeting-script-integrate` | Persistir artefato e atualizar agent/config | Worker |
| 5 | `create-greeting-script-validate` | Executar quality gate e checklist | Worker |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Nome do squad alvo |
| `entry_agent` | string | No | Entry agent explícito; se ausente, ler do `config.yaml` |

## Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Greeting script | `squads/{squad}/scripts/generate-{squad}-greeting.cjs` | Script executável final |
| Agent update | `squads/{squad}/agents/{entry_agent}.md` | STEP 3.5 atualizado |
| Validation report | `runtime_context` | Veredito final do quality gate |

## Veto Conditions

- Script sem `inferNextAction()` -> bloquear
- `Next Action` genérica quando há blocker -> bloquear
- Ausência de Runtime Directives -> bloquear
- Geração sem template base -> bloquear

## Commands

```yaml
commands:
  standard: "*create-greeting-script {squad_name}"
  agent_override: "*create-greeting-script {squad_name} --agent {entry_agent}"
  audit: "*create-greeting-script {squad_name} --audit"
```

## Acceptance Criteria

- [ ] Script `.cjs` gerado e funcional
- [ ] Runtime Directives block presente
- [ ] Next Action com severity icon presente
- [ ] Entry agent atualizado com STEP 3.5
- [ ] `checklists/greeting-script-checklist.md` PASS

## Related Documents

- `workflows/wf-create-greeting-script.yaml`
- `templates/greeting-script-tmpl.cjs`
- `checklists/greeting-script-checklist.md`

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
