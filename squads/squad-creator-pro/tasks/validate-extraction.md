---
task-id: validate-extraction
name: "Validate Extraction Quality"
version: 2.0.0
execution_type: Orchestrator
model: Haiku
model_rationale: "Orchestrator stub -- delegates to 3 atomic sub-tasks. Haiku for routing."
haiku_eligible: true
note: "Decomposed from v1.0.0 monolith (359 lines, 11-point checklist) into 3 atomic tasks."
estimated-time: 20-30 min
complexity: medium

inputs:
  required:
    - expert_name: "Nome do expert avaliado"
    - extraction_files: "Arquivos de extracao a validar"

outputs:
  primary:
    - validation_report: "Relatorio com 11 itens, gate decision, e handoff package"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-extraction
  task_name: Validate Extraction Quality
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 20-30m
  domain: Operational
  input:
  - '{''expert_name'': ''Nome do expert avaliado''}'
  - '{''extraction_files'': ''Arquivos de extracao a validar''}'
  output:
  - '{''validation_report'': ''Relatorio com 11 itens, gate decision, e handoff package''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Relatorio com 11 itens, gate decision, e handoff package'
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
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Validate Extraction Quality

> **Self-Validation Gate** | Checklist antes de handoff para @pedro-valerio
>
> **Regra:** Se falhar, LOOP -- nao handoff.

---

## Checklist Reference

Before marking this task complete, verify against: `checklists/sop-validation.md`

---

## Pipeline (3 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `validate-extraction-checklist` | Run 11-Point Checklist | 10 min |
| 2 | `validate-extraction-adversarial` | Cross-Source & Adversarial Tests | 10 min |
| 3 | `validate-extraction-gate` | Gate Decision & Handoff/Loop | 5 min |

---

## Execution Flow

```
validate-extraction-checklist
  | checklist_results (11 items scored)
  v
validate-extraction-adversarial
  | adversarial_results, cross_source_patterns
  v
validate-extraction-gate
  | validation_report, gate_decision (FINAL OUTPUT)
  v
[PASS → HANDOFF to @pedro-valerio]
[FAIL → LOOP with identified gaps]
```

---

## Gate: FRAMEWORK_HANDOFF_READY

```yaml
checkpoint_clareza_handoff:
  question: "Insumos como um TODO trazem CLAREZA ou CONFUSAO?"
  if_clareza: "HANDOFF para PV"
  if_confusao: "LOOP - simplificar antes de entregar"

checkpoint_pareto_identificado:
  question: "0.8% do expert esta identificado e documentado?"
  if_sim: "Handoff pode prosseguir"
  if_nao: "VETO - executar find-0-8 antes de handoff"

checkpoint_depth_not_breadth:
  question: "Insumos refletem PROFUNDIDADE ou VOLUME?"
  if_profundidade: "Handoff com qualidade depth-first"
  if_volume: "LOOP - reduzir volume, aumentar profundidade"
```

---

## Completion Criteria

| Criterio | Status |
|----------|--------|
| Todos 11 itens do checklist verificados | [ ] |
| Evidencia documentada para cada item | [ ] |
| Se FAIL: gaps identificados e acao definida | [ ] |
| Se PASS: handoff package listado | [ ] |

---

*"PV nao pode operacionalizar inferencias. So entrega com 15+ citacoes verificaveis."*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** expert_name; extraction_files
- **Outputs:** Relatorio com 11 itens, gate decision, e handoff package
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] Output artifact produced: Relatorio com 11 itens, gate decision, e handoff package
- [ ] Task output validated against quality standards
