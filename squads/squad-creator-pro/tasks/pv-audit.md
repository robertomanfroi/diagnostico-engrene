<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: pv-audit
  task_name: Process Audit (Stub)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Phase 1 complete with structural overview
  - Phase 2 complete with sample analysis
  - Token budget respected (< 10k total)
  - User directed deep-dives (if necessary)
  - Veto conditions proposed for problems found
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Process Audit (Stub)

> Pedro Valerio | Loaded on-demand when `*audit {squad}` is invoked

**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

## Purpose

Auditar squad/workflow por falhas de processo usando framework "Impossibilitar Caminhos"

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-PVA-001 | Audit must not exceed 10k token budget | Track cumulative: Phase 1 ~2k + Phase 2 ~5k + Phase 3 ~3k = 10k max | VETO - BLOCK |
| VETO-PVA-002 | Must not read all agent files at once | No more than 3 files per phase | VETO - BLOCK |
| VETO-PVA-003 | Deep-dive must not execute without user direction | User must explicitly request specific analysis | VETO - BLOCK |

---

## Input

- Squad name or workflow file path
- `--all` flag for 100% audit (with batching)

## Parameters

| Flag | Behavior |
|------|----------|
| (default) | 3-Phase Staged -- sample representativo |
| `--all` | Audit 100% in batches of 3 agents |

---

## Sub-Tasks (Atomic Execution)

| # | Sub-Task | File | Responsibility |
|---|----------|------|----------------|
| 1 | Overview | `pv-audit-overview.md` | Structural overview without reading content (~2k tokens) |
| 2 | Sample Analysis | `pv-audit-sample.md` | Pattern identification with representative sample (~5k tokens) |
| 3 | Deep-Dive | `pv-audit-deep-dive.md` | On-demand analysis of specific agent/workflow/dna (~3k tokens) |

---

## Execution Flow

```
Step 1: pv-audit-overview (Phase 1)
  Input: squad name
  Output: squad_overview YAML (structure, counts, sizes)
  HALT: Show overview, ask user for direction

Step 2: pv-audit-sample (Phase 2)
  Input: squad_overview
  Output: sample_analysis YAML (patterns, red/green flags)
  HALT: Show analysis, ask if user wants deep-dive

Step 3: pv-audit-deep-dive (Phase 3, on-demand)
  Input: specific agent/workflow name from user
  Output: deep_dive YAML (wrong paths, veto proposals, verdict)
```

---

## Mode: Full Audit (`--all`)

When `--all` flag is used, pv-audit-sample runs in batches of 3 agents with user confirmation between batches. See `pv-audit-sample.md` for batch execution details.

---

## Final Report (after all phases)

```yaml
audit_report:
  squad: "{name}"
  date: "{date}"
  auditor: "@pedro-valerio"
  scope:
    agents_total: N
    agents_sampled: N
    coverage: "X%"
  token_usage:
    phase_1: "~Xk"
    phase_2: "~Xk"
    phase_3: "~Xk (if applicable)"
    total: "~Xk / 10k budget"
  findings:
    critical: []
    major: []
    minor: []
  verdict: "PASS | NEEDS WORK | REDESIGN"
  next_actions: []
```

---

## Completion Criteria

- [ ] Phase 1 complete with structural overview
- [ ] Phase 2 complete with sample analysis
- [ ] Token budget respected (< 10k total)
- [ ] User directed deep-dives (if necessary)
- [ ] Veto conditions proposed for problems found

---

_Task Version: 2.0.0_
_Atomized: 2026-03-26_
_Sub-tasks: pv-audit-overview, pv-audit-sample, pv-audit-deep-dive_

## Task Anatomy

- **Executor:** Agent
- **Inputs:** Task-specific context and prior pipeline outputs
- **Outputs:** Completed pv-audit output artifact
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] Phase 1 complete with structural overview
- [ ] Phase 2 complete with sample analysis
- [ ] Token budget respected (< 10k total)
- [ ] User directed deep-dives (if necessary)
- [ ] Veto conditions proposed for problems found
