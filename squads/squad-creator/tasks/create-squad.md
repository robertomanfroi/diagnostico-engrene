# Task: Create Complete Squad (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad` |
| **Version** | `5.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: create-squad
name: "Create Complete Squad"
category: squad-creation
agent: squad-chief
elicit: true
autonomous: false
type: composed
description: "Orchestrates 5 sub-tasks to create a complete AIOX-FULLSTACK squad through discovery, design, build, validation, and publish."
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_squad
Output: artifact::create_squad
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

This is a **composed task** that orchestrates sub-tasks in sequence. Each sub-task is a cohesive unit of work that can be executed, tested, and maintained independently. v5.0.0 de-atomized the previous 8-task pipeline into 5 focused tasks by merging steps that naturally belong together.

## PRO DETECTION

> At execution time, check if `squads/squad-creator-pro/workflows/wf-create-squad.yaml` exists.
> If YES and pro mode is active, delegate to pro workflow override.
> If NO, continue with this base version.

## Context-First Entrypoint

Run `detect-squad-context` first. Route to the appropriate workflow based on context type before executing this sequence.

## Execution Sequence

```
[1] create-squad-discover  — Discovery & Type Selection
[2] create-squad-design    — Architecture & Scaffold
[3] create-squad-build     — Components & Integration
[4] create-squad-validate  — Quality Loop (Validate + Fix + Optimize)
[5] create-squad-publish   — Activation Surfaces & Smoke Test
```

Each sub-task receives the output of the previous task as input. A blocking veto in any sub-task halts the entire pipeline.

## Sub-Task Reference

| # | Task ID | Phase | Checkpoint | Blocking | Merged From |
|---|---------|-------|------------|----------|-------------|
| 1 | `create-squad-discover` | Discovery & Type Selection | SC_DSC_001 | Yes | discover + select-type |
| 2 | `create-squad-design` | Architecture & Scaffold | SC_ARC_001 | Yes | architecture + scaffold |
| 3 | `create-squad-build` | Components & Integration | SC_CRT_001 | Yes | components + integrate |
| 4 | `create-squad-validate` | Quality Loop | SC_VAL_001 | Yes | validate + fix + optimize |
| 5 | `create-squad-publish` | Publish & Smoke Test | SC_PUB_001 | Yes | publish + smoke-test |

## Frameworks Used

- `data/tier-system-framework.md` — Agent tier classification (Design)
- `data/quality-dimensions-framework.md` — Squad validation (Validate)
- `data/decision-heuristics-framework.md` — Checkpoint logic (Design, Validate)
- `data/executor-matrix-framework.md` — Task executor assignment (Build)
- `data/squad-type-definitions.yaml` — Squad type catalog (Discover)

## Veto Conditions (Aggregated)

| ID | Condition | Sub-Task |
|----|-----------|----------|
| VETO-SQD-001 | Overwrite without confirmation | discover |
| VETO-SQD-002 | Quality score < 7.0 after retries | validate |
| VETO-SQD-003 | Missing entry agent | build |
| VETO-SQD-004 | Missing workspace integration level | design |
| VETO-SQD-005 | Direct workspace mutation | build |
| VETO-SQD-006 | Smoke test failure | publish |

## Error Handling

```yaml
error_handling:
  sub_task_failure:
    - log failure context and sub-task ID
    - attempt automated fix within sub-task (max_retries per sub-task)
    - if unrecoverable: halt pipeline, report to human
  resume:
    - check runtime state at .aiox/squad-runtime/create-squad/{squad_name}/state.json
    - resume from last completed sub-task
```

---

_Task Version: 5.0.0 (de-atomized from v4.0.0: 8 tasks -> 5 tasks)_
_Last Updated: 2026-03-27_
