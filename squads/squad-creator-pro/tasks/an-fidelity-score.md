---
task-id: an-fidelity-score
name: "Fidelity Score"
version: 4.0.0
execution_type: Orchestrator
model: Haiku
model_rationale: "Orchestrator stub -- delegates to 1 task. 95% deterministic via worker script."
haiku_eligible: true
note: "De-atomized from v3.0.0 (3 subtasks) into 1 merged task. identify + layers were pure mechanical work."
estimated-time: 10-15 min
complexity: medium

inputs:
  required:
    - clone_path: "Path to the clone agent file"

outputs:
  primary:
    - fidelity_report: "Complete fidelity report with scores, classification, and gaps"

worker_script: "scripts/fidelity-score.sh"
load: "data/an-clone-validation.yaml"
elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-fidelity-score
  task_name: Fidelity Score
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 15-20m
  domain: Operational
  input:
  - '{''clone_path'': ''Path to the clone agent file''}'
  output:
  - '{''fidelity_report'': ''Complete fidelity report with scores, classification,
    and gaps''}'
  action_items:
  - Resolve Canonical Workflow
  - Delegate to Calculate Task
  - Reconcile Final Fidelity Report
  acceptance_criteria:
  - '`wf-fidelity-score.yaml` existe e permanece owner canônico [threshold: >= 1]'
  - '`an-fidelity-score-calculate.md` executa o preflight e o score completo [threshold: >= 1]'
  - o wrapper não duplica a metodologia das 8 camadas [threshold: >= 1]
  - fidelity_report final é reconciliado a partir do workflow [threshold: >= 1]
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


# Fidelity Score

**Task ID:** an-fidelity-score  
**Version:** 4.1.0  
**Purpose:** manter o entrypoint de fidelity scoring como contrato curto enquanto `wf-fidelity-score.yaml` e `an-fidelity-score-calculate.md` executam o pipeline real

## Canonical Owner

- `squads/squad-creator-pro/workflows/wf-fidelity-score.yaml`
- `squads/squad-creator-pro/tasks/an-fidelity-score-calculate.md`

## Inputs

- `clone_path` é obrigatório

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-fidelity-score.yaml` existe
- [ ] `squads/squad-creator-pro/tasks/an-fidelity-score-calculate.md` existe
- [ ] o chamador entende que o preflight via `scripts/fidelity-score.sh` é executado pela task calculadora, não manualmente neste wrapper

## Execution Contract

```yaml
resolve_workflow:
  workflow: "squads/squad-creator-pro/workflows/wf-fidelity-score.yaml"
  phases:
    - orchestrate
    - calculate-and-report

delegate_to_calculate_task:
  task: "squads/squad-creator-pro/tasks/an-fidelity-score-calculate.md"
  payload:
    - clone_path
  task_owns:
    - identify_clone_files
    - run_preflight_script
    - validate_8_layers_x_5_checkpoints
    - calculate_weighted_score
    - classify_and_generate_report

reconcile_outputs:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-fidelity-score.yaml"
  calculate_task: "squads/squad-creator-pro/tasks/an-fidelity-score-calculate.md"
  final_report: "fidelity_report"
  status: "delegated"
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-fidelity-score.yaml"
  calculate_task: "squads/squad-creator-pro/tasks/an-fidelity-score-calculate.md"
  final_report: "fidelity_report"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `wf-fidelity-score.yaml` permanece como owner canônico [threshold: >= 1]
- [ ] `an-fidelity-score-calculate.md` executa o preflight e o score completo [threshold: >= 1]
- [ ] o wrapper não duplica a metodologia das 8 camadas [threshold: >= 1]
- [ ] o `fidelity_report` final é reconciliado a partir do workflow [threshold: >= 1]
