<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-validate-clone
  task_name: Validate Clone (Orchestrator)
  status: pending
  responsible_executor: Worker
  execution_type: Hybrid
  estimated_time: 45m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Resolve Canonical Workflow
  - Consume Fidelity and Hackability Inputs
  - Produce Final Verdict and Report
  acceptance_criteria:
  - '`wf-validate-clone.yaml` existe e permanece owner canônico [threshold: >= 1]'
  - '`an-fidelity-score.md` fornece o fidelity score sem duplicação [threshold: >= 1]'
  - '`an-validate-clone-hackability.md` executa hackability e authenticity [threshold: >= 1]'
  - o wrapper finaliza veredito e report sem repetir as fases anteriores [threshold: >= 1]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Validate Clone (Orchestrator)

**Task ID:** an-validate-clone  
**Version:** 3.1.0  
**Purpose:** fechar o veredito e o relatório final de validação usando os outputs já produzidos por `wf-validate-clone.yaml`

## Canonical Owner

- `squads/squad-creator-pro/workflows/wf-validate-clone.yaml`
- `squads/squad-creator-pro/tasks/an-fidelity-score.md`
- `squads/squad-creator-pro/tasks/an-validate-clone-hackability.md`

## Inputs

- `clone_path` é obrigatório no entrypoint do workflow
- `fidelity_scores`, `hackability_results` e `authenticity_markers` chegam das fases anteriores

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-validate-clone.yaml` existe
- [ ] `an-fidelity-score.md` e `an-validate-clone-hackability.md` existem
- [ ] o chamador entende que este wrapper finaliza o verdict/report e não repete fidelity ou hackability

## Execution Contract

```yaml
resolve_workflow:
  workflow: "squads/squad-creator-pro/workflows/wf-validate-clone.yaml"
  phases:
    - fidelity-score
    - hackability-authenticity
    - verdict-report

consume_dependencies:
  fidelity_task: "squads/squad-creator-pro/tasks/an-fidelity-score.md"
  hackability_task: "squads/squad-creator-pro/tasks/an-validate-clone-hackability.md"
  required_inputs:
    - fidelity_scores
    - hackability_results
    - authenticity_markers

finalize_verdict:
  outputs:
    - validation_verdict
    - validation_report
  rule: "apply the deterministic decision tree using workflow inputs already produced upstream"
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-validate-clone.yaml"
  verdict: "validation_verdict"
  report: "validation_report"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `wf-validate-clone.yaml` permanece como owner canônico [threshold: >= 1]
- [ ] `an-fidelity-score.md` fornece o fidelity score sem duplicação [threshold: >= 1]
- [ ] `an-validate-clone-hackability.md` executa hackability e authenticity [threshold: >= 1]
- [ ] o wrapper finaliza veredito e report sem repetir as fases anteriores [threshold: >= 1]
