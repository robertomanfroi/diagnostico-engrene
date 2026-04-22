<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: batch-closeout
  task_name: Batch Closeout
  status: pending
  responsible_executor: Human
  execution_type: Human
  estimated_time: 1h
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Parity snapshot generated (base vs pro path comparison with counts)
  - Identical duplicates identified or explicitly exempted with rationale
  - Legitimate overrides classified (each override has a documented reason)
  - Shadow stale paths classified (paths that exist in pro but are unused/orphaned)
  - Batch size <= 25 paths (if exceeded, split into sub-batches and run this gate
    per sub-batch)
  output_persistence: transient_output
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Human
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Batch Closeout

Formalizes the 3 partial SINKRA contract quality gates (QG-SCP-003, QG-SCP-005, QG-SCP-008) as a sequential operator checklist. Run this task at the end of any maintenance batch (sync, refactor, atomization round) before marking the batch as done.

## Task Anatomy

- **Executor:** Human
- **Trigger:** End of any maintenance batch (sync, refactor, atomization round)
- **Inputs:** Completed batch work (refactored files, updated registries, parity snapshots), current disk inventory, story file, README/docs
- **Outputs:** All 3 gate checklists passed, batch marked done
- **Completion Criteria:** Every checkbox in Gates 1-3 is checked; no gate has an unchecked item without an explicit waiver logged in the story
- **Guardrails:** All 3 gates must pass before the batch is marked done. A single unchecked item without a documented waiver blocks closeout.

---

## Gate 1: Parity Audit (QG-SCP-003)

Transition gate between audit and refactor within a maintenance batch.

- [ ] Parity snapshot generated (base vs pro path comparison with counts)
- [ ] Identical duplicates identified or explicitly exempted with rationale
- [ ] Legitimate overrides classified (each override has a documented reason)
- [ ] Shadow stale paths classified (paths that exist in pro but are unused/orphaned)
- [ ] Batch size <= 25 paths (if exceeded, split into sub-batches and run this gate per sub-batch)

---

## Gate 2: Refactor Safety & Ownership (QG-SCP-005)

Handoff gate between refactor and runtime/compliance validation.

- [ ] No runtime-native file converted to wrapper by mistake (verify each refactored file retains its original classification)
- [ ] No authoritative registry removed (all registries present before the batch still exist)
- [ ] All same-path paths have explicit `owner_category` (base, pro, or shared) in the executor matrix or equivalent
- [ ] Adapters preserve legacy contract (any adapter/wrapper still honors its original interface and behavior)

---

## Gate 3: Closeout & Traceability (QG-SCP-008)

Exit gate at batch closeout.

- [ ] Stats reconciled with disk (inventory counts match actual file system -- run `find` or equivalent and compare)
- [ ] Drift registered (any delta between expected and actual state is logged in the score card or compliance report)
- [ ] Story updated (story file reflects completed work, checkboxes marked, file list current)
- [ ] README/docs updated or explicitly marked as "no changes required" in the story change log

---

## Acceptance Criteria

- [ ] All Gate 1 checkboxes are checked or waived with documented rationale
- [ ] All Gate 2 checkboxes are checked or waived with documented rationale
- [ ] All Gate 3 checkboxes are checked or waived with documented rationale
- [ ] Batch is only marked done after all 3 gates pass
- [ ] Any waiver is logged in the story change log with reason and approver
