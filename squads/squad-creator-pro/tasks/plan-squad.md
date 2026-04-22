<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: plan-squad
  task_name: Plan Squad with Deep PRD
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Strategic
  action_items:
    - Resolve Planning Contract
    - Calibrate Depth
    - Map Domain
    - Design Architecture
    - Challenge and Reorder
    - Define Roadmap
    - Assemble PRD
  acceptance_criteria:
    - "docs/projects/{domain}/prd.md existe"
    - "o workflow wf-plan-squad.yaml referencia task_ref específico por fase"
    - "o plano registra alternativas, order rationale e open questions"
  output_persistence: transient_output
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

# Task: Plan Squad with Deep PRD

**Task ID:** plan-squad  
**Version:** 3.1.0  
**Purpose:** compor o planejamento profundo do squad via subtasks por fase, sem manter um monólito de 300+ linhas

## Canonical Workflow

- `workflows/wf-plan-squad.yaml`

## Atomic Sub-Tasks

- `plan-squad-contract.md`
- `plan-squad-depth-calibration.md`
- `plan-squad-domain-mapping.md`
- `plan-squad-architecture.md`
- `plan-squad-challenge-reorder.md`
- `plan-squad-roadmap.md`
- `plan-squad-prd-assembly.md`

## Inputs

- `domain` é obrigatório
- `purpose`, `target_user`, `reference`, `output`, `business`, `product` e `app` refinam o planejamento

## Preconditions

- [ ] `workflows/wf-plan-squad.yaml` existe
- [ ] o template `squad-prd-deep-tmpl.md` existe
- [ ] o chamador entende que `plan-squad` agora é tarefa composta

## Execution Sequence

```text
[1] plan-squad-contract
[2] plan-squad-depth-calibration
[3] plan-squad-domain-mapping
[4] plan-squad-architecture
[5] plan-squad-challenge-reorder
[6] plan-squad-roadmap
[7] plan-squad-prd-assembly
OUTPUT: docs/projects/{domain}/prd.md + planning-summary.yaml
```

## Acceptance Criteria

- [ ] o workflow usa `task_ref` específico por fase
- [ ] o PRD final cobre problema, capacidades, arquitetura, governança, roadmap e riscos
- [ ] alternativas, `not_before_conditions` e `why this order` são explicitados
