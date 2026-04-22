# Task: Auto-Heal (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-heal` |
| **Version** | `3.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: auto-heal
name: "Auto-Heal"
category: runtime
agent: squad-chief
elicit: false
autonomous: true
description: "Task composta que orquestra 2 subtasks para resolver (diagnosticar + fix/escalar) e fechar (verificar + persistir + veredito) erros operacionais."
owner_workflow: "workflows/wf-auto-heal.yaml"
template_source: "templates/auto-heal-task-tmpl.md"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::auto_heal
Output: artifact::auto_heal
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Recuperar erros operacionais de forma segura, com persistência de trilha
auditável e escalada explícita quando o fix automático não for apropriado.

## Execution Sequence

```text
INPUT (error_message + error_source? + squad_name?)
    |
[1] auto-heal-resolve
    -> Diagnostica erro, aplica fix seguro ou escala para ação humana
    |
[2] auto-heal-close
    -> Verifica resultado, persiste trilha auditável, emite veredito final
    |
OUTPUT: heal_verdict
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `auto-heal-resolve` | Diagnóstico + fix seguro ou escalada | Hybrid |
| 2 | `auto-heal-close` | Verificação + persistência + veredito final | Worker |

## Commands

```yaml
commands:
  diagnose: "*auto-heal --diagnose {error_context}"
  fix: "*auto-heal --fix {error_context}"
  history: "*auto-heal --history"
```

## Related Documents

- `workflows/wf-auto-heal.yaml`
- `templates/auto-heal-task-tmpl.md`
- `operational-test.md`

---

_Task Version: 3.0.0_
