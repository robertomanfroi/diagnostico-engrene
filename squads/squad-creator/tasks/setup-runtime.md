# Task: Setup Runtime (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `setup-runtime` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: setup-runtime
name: "Setup Runtime"
category: runtime
agent: squad-chief
elicit: true
autonomous: false
description: "Composed task that orchestrates 5 atomic sub-tasks to configurar e validar runtime operacional."
owner_workflow: "workflows/wf-setup-runtime.yaml"
template_source: "templates/setup-runtime-task-tmpl.md"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::setup_runtime
Output: artifact::setup_runtime
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Configurar conexões de runtime para squads operacionais, validar o acesso real às
APIs e persistir o baseline inicial de operação.

## Execution Sequence

```
INPUT (squad_name + required_apis + validation_mode)
    |
[1] setup-runtime-requirements
    -> Carrega api-requirements e categoriza prioridades
    |
[2] setup-runtime-wizard
    -> Coleta credenciais e confirma skips permitidos
    |
[3] setup-runtime-validate
    -> Testa conexões configuradas e aplica política de bloqueio
    |
[4] setup-runtime-persist
    -> Atualiza .env, backup dedicado e runtime-baseline.yaml
    |
[5] setup-runtime-handoff
    -> Resume o setup e prepara handoff para operational-test
    |
OUTPUT: runtime_handoff
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `setup-runtime-requirements` | Normalizar requisitos do runtime | Worker |
| 2 | `setup-runtime-wizard` | Coletar credenciais | Hybrid |
| 3 | `setup-runtime-validate` | Validar conexões | Agent |
| 4 | `setup-runtime-persist` | Persistir baseline e variáveis | Worker |
| 5 | `setup-runtime-handoff` | Preparar próximo passo | Agent |

## Commands

```yaml
commands:
  full_setup: "*setup-runtime"
  single_api: "*setup-runtime --api={api_name}"
  validate: "*setup-runtime --validate"
  status: "*setup-runtime --status"
  refresh: "*setup-runtime --refresh {api_name}"
  reset: "*setup-runtime --reset"
```

## Related Documents

- `workflows/wf-setup-runtime.yaml` -- Workflow canônico
- `templates/setup-runtime-task-tmpl.md` -- Fonte usada para squads gerados
- `operational-test.md` -- Próximo passo canônico

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
_Sub-tasks: 5 atomic tasks_
