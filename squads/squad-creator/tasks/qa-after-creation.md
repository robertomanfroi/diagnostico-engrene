# Task: QA After Creation (Orchestrator)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-after-creation` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: qa-after-creation
name: QA After Creation
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Orchestrator for post-creation QA pipeline. Delegates to 6 atomic tasks
  in sequence. Any ABORT/FAIL in early tasks short-circuits the pipeline.
accountability:
  human: squad-operator
  scope: full
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::qa_after_creation
Output: artifact::qa_after_creation
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Automatic quality assurance after squad/component creation. This task orchestrates 6 atomic checks and produces a final QA report with score and verdict.

## When This Task Runs

| Trigger Task | What Was Created | QA Scope |
|--------------|------------------|----------|
| `*create-squad` | New squad | Full squad validation |
| `*create-agent` | New agent | Agent-only validation |
| `*create-task` | New task | Task-only validation |
| `*create-workflow` | New workflow | Workflow-only validation |
| `*create-template` | New template | Template-only validation |

## Inputs

```yaml
inputs:
  created_component:
    type: string
    required: true
    description: "Path to created component"
  component_type:
    type: enum
    required: true
    values: ["squad", "agent", "task", "workflow", "template"]
  creation_task:
    type: string
    required: false
  auto_fix:
    type: boolean
    default: false
```

## Pipeline

```
1. qa-check-structure    -- Directory layout, required files, syntax, metadata
       |
       | ABORT? --> FAIL (short-circuit)
       v
2. qa-check-schema       -- Field types, required sections, enum values
       |
       | FAIL? --> FAIL (short-circuit)
       v
3. qa-check-references   -- Cross-references, handoff targets, dependency chains
       |
       | FAIL? --> FAIL (short-circuit)
       v
4. qa-check-completeness -- Quality scoring (weighted criteria, 0-10 scale)
       |
       v
5. qa-check-compatibility -- Security scan, governance framework, conventions
       |
       | HIGH security? --> FAIL (short-circuit)
       v
6. qa-generate-report    -- Aggregate, score, verdict, report file, actions
```

## Thresholds

| Score | Verdict | Action |
|-------|---------|--------|
| >= 7.0 | PASS | Mark validated, create badge |
| >= 5.0 | CONDITIONAL | Warn, ask to proceed |
| < 5.0 | FAIL | Block, list fixes |

## Outputs

| Output | Location |
|--------|----------|
| QA Report | Console (immediate) |
| Report File | `{component}/docs/qa-report-{date}.md` |
| Validation Badge | `{component}/docs/VALIDATED.md` (if PASS) |

## Related Tasks

| Task | Purpose |
|------|---------|
| `qa-check-structure` | Phase 0+1: structure and quick checks |
| `qa-check-schema` | Phase 2: schema validation |
| `qa-check-references` | Phase 3: cross-reference validation |
| `qa-check-completeness` | Phase 4: quality scoring |
| `qa-check-compatibility` | Phase 5: security and framework compliance |
| `qa-generate-report` | Phase 6: report generation and actions |
| `validate-squad` | Full squad validation (called by completeness) |
| `fix-issues` | Attempt to fix QA issues |
