# Task: Discover Tools for Squad (Orchestrator)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools` |
| **Version** | `4.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: discover-tools
name: "Discover Tools for Squad"
category: discovery
agent: squad-chief
elicit: true
autonomous: false
description: >
  Orchestrator task that coordinates the 5 atomic discovery subtasks.
  Research and discover MCP servers that can potentialize squad deliverables.
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::discover_tools
Output: artifact::discover_tools
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Orchestrate the tool discovery pipeline by executing five atomic subtasks
in sequence. Each subtask has a single responsibility and produces
structured output consumed by the next.

## PRO DETECTION

> At execution time, check if `squads/squad-creator-pro/workflows/wf-discover-tools.yaml` exists.
> If YES and pro mode is active: delegate to pro workflow override.
> If NO: continue with this base version.

## Pipeline

```
INPUT (domain + use_cases + existing_capabilities)
    |
[1. SCAN]         discover-tools-scan.md
    |              Domain validation + internal scan + gap analysis
[2. CLASSIFY]     discover-tools-classify.md
    |              Search MCP sources + classify findings
[3. EVALUATE]     discover-tools-evaluate.md
    |              Score, filter, rank qualified tools
[4. RECOMMEND]    discover-tools-recommend.md
    |              Impact/effort matrix + integration plan
[5. REPORT]       discover-tools-report.md
    |              Final report + capability map + plan files
OUTPUT: Tool Discovery Report + Capability Map
```

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `domain` | string | Yes | Squad domain |
| `use_cases` | list | Yes | Key squad use cases |
| `existing_tools` | list | No | Tools already in use |
| `capability_gaps` | list | No | Known capability gaps |
| `budget_tier` | enum | No | `"free_only"`, `"low_cost"`, `"enterprise"` |
| `scope_hint` | string | No | Clarification for ambiguous domains |

## Subtask Execution Order

| # | Task ID | Blocking | Output |
|---|---------|----------|--------|
| 1 | `discover-tools-scan` | Yes | `scan-results.yaml` |
| 2 | `discover-tools-classify` | Yes | `classified-tools.yaml` |
| 3 | `discover-tools-evaluate` | Yes | `evaluated-tools.yaml` |
| 4 | `discover-tools-recommend` | Yes (elicit) | `recommendations.yaml` |
| 5 | `discover-tools-report` | Yes | Report + Map + Plan |

Each subtask MUST complete before the next begins. If any subtask triggers
a veto condition, the pipeline halts and reports the block reason.

## Outputs

| Output | Location |
|--------|----------|
| Tool Discovery Report | `.aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md` |
| Capability Map | `.aiox/squad-runtime/discovery/{domain}/capability-tools.yaml` |
| Integration Plan | `.aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md` |

## Heuristics Reference

| ID | Name | Subtask | Blocking |
|----|------|---------|----------|
| SC_DCV_001 | Domain Context Validation | scan | Yes |
| SC_INT_001 | Internal Coverage Gate | scan | Yes |
| SC_MCP_001 | MCP Discovery Gate | classify | No |
| SC_TDR_001 | Tool Discovery Report | report | Yes |

## Error Handling

```yaml
error_handling:
  subtask_fails:
    action: "Log failure, report which subtask and why"
    fallback: "Allow partial results up to last successful subtask"
  search_fails:
    action: "Try alternative queries"
    fallback: "Mark gap as 'manual research needed'"
  no_tools_found:
    action: "Expand to adjacent domains"
    fallback: "Document as 'custom development needed or check pro version'"
```

## Frameworks Used

- `data/quality-dimensions-framework.md` -- Tool quality scoring
- `data/decision-heuristics-framework.md` -- Tool selection logic
- `protocols/ai-first-governance.md` -- Canonical scope validation

---

_Task Version: 4.0.0 (decomposed from v3.0 monolith)_
_Last Updated: 2026-03-26_
_Subtasks: discover-tools-scan, discover-tools-classify, discover-tools-evaluate, discover-tools-recommend, discover-tools-report_
