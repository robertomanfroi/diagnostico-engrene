<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-from-sop
  task_name: Create Squad Artifacts From Workspace SOPs (Stub)
  status: pending
  responsible_executor: '@pedro-valerio'
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
  - Loader executado com `business` explicito e seletores explicitos
  - Nenhuma fonte fora de `workspace/businesses/{slug}` foi considerada valida
  - runtime_mode` validado como `full_workspace_mode
  - source_of_truth` validado como `workspace_canonical
  - Cada processo executavel virou task candidate com executor + guardrails
  output_persistence: canonical_workspace
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


# Task: Create Squad Artifacts From Workspace SOPs (Stub)

**Task ID:** create-from-sop
**Purpose:** Carregar SOPs YAML canonicos de `workspace/businesses/{slug}` e transformar em artefatos de criacao de squad
**Orchestrator:** @pedro-valerio
**Mode:** Business-aware operationalization
**Pattern:** SC-PV-SOP-001
**Execution Type:** `Agent`
**Model:** `Opus` (cross-file synthesis de processos canonicos)
**Haiku Eligible:** NO

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CFS-001 | Business slug must be explicit | Verify `--business=<slug>` is present | VETO - BLOCK |
| VETO-CFS-002 | Environment contract must resolve to `full_workspace_mode` | Run `load-business-sops.cjs` and verify `runtime_mode == full_workspace_mode` | VETO - BLOCK |
| VETO-CFS-003 | Source of truth must be `workspace_canonical` | Verify loader output `source_of_truth == workspace_canonical` | VETO - BLOCK |
| VETO-CFS-004 | User must explicitly define at least one SOP selector | Verify `--namespace=<dir>` and/or `--paths=<a,b>` is present | VETO - BLOCK |
| VETO-CFS-005 | Every selector must resolve inside `workspace/businesses/{slug}` | Verify loader returns zero `missing_requested_sources` | VETO - BLOCK |

## Checklist Reference

Before marking this task complete, verify against: `checklists/quality-gate-checklist.md`

---

## Command

```text
*create-from-sop --business={slug} --namespace=L1-strategy [--namespace=L3-product/{product}] [--paths=L1-strategy/team-structure.yaml]
```

---

## Sub-Tasks (Atomic Execution)

| # | Sub-Task | File | Responsibility |
|---|----------|------|----------------|
| 1 | Load + Classify | `create-from-sop-load-classify.md` | Run loader, validate environment, classify sources into 3 classes |
| 2 | Map + Workflow | `create-from-sop-map-workflow.md` | Extract processes, synthesize workflows, surface gaps |
| 3 | Brief | `create-from-sop-brief.md` | Generate creation brief with all artifacts |

---

## Execution Flow

```
Step 1: create-from-sop-load-classify
  Input: --business + --namespace/--paths
  Output: classified sources (executable_process, supporting_context, governance_signal)

Step 2: create-from-sop-map-workflow
  Input: classified sources
  Output: task inventory + workflow map + open questions

Step 3: create-from-sop-brief
  Input: all artifacts from steps 1-2
  Output: squad_creation_brief + output contract YAML
```

---

## Acceptance Criteria

- [ ] Loader executado com `business` explicito e seletores explicitos
- [ ] Nenhuma fonte fora de `workspace/businesses/{slug}` foi considerada valida
- [ ] `runtime_mode` validado como `full_workspace_mode`
- [ ] `source_of_truth` validado como `workspace_canonical`
- [ ] Cada processo executavel virou task candidate com executor + guardrails
- [ ] Contexto de suporte foi separado de processo executavel
- [ ] Gaps ficaram marcados sem invencao

---

_Task Version: 2.0.0_
_Atomized: 2026-03-26_
_Sub-tasks: create-from-sop-load-classify, create-from-sop-map-workflow, create-from-sop-brief_

## Task Anatomy

- **Executor:** Agent
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed create-from-sop output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
