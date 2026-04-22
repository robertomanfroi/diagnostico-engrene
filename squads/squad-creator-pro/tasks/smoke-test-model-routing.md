<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: smoke-test-model-routing
  task_name: smoke-test-model-routing
  status: pending
  responsible_executor: Worker
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Pre-flight Check (via script)
  - Validate Task Lookup (3 samples)
  - Execution Test (Haiku Task)
  - Comparison Test (Without model param)
  - Generate Report
  acceptance_criteria:
  - 'Phase 1: All pre-flight checks pass'
  - 'Phase 2: All 3 task lookups return correct tier'
  - 'Phase 3: Haiku task completes successfully'
  - 'Phase 4: Comparison shows difference (or confirms behavior)'
  - 'Phase 5: Report generated with at least 1 logged entry'
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: smoke-test-model-routing

**Task ID:** smoke-test-model-routing  
**Version:** 3.1.0  
**Purpose:** compor o smoke test de model routing em fases atômicas de preflight, lookup, execução explícita, comparação e report

## Canonical Workflow

- `squads/squad-creator-pro/workflows/wf-smoke-test-model-routing.yaml`

## Atomic Sub-Tasks

- `smoke-test-model-routing-preflight.md`
- `smoke-test-model-routing-lookup.md`
- `smoke-test-model-routing-execution.md`
- `smoke-test-model-routing-comparison.md`
- `smoke-test-model-routing-report.md`

## Inputs

- `config/model-routing.yaml` e os scripts de validator/logger são obrigatórios
- `metrics/` precisa estar disponível para logging
- a fase de comparação depende do teste explícito concluído

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-smoke-test-model-routing.yaml` existe
- [ ] as 5 subtasks atômicas existem
- [ ] o preflight gera `/tmp/preflight-model-routing.txt` antes de qualquer validação manual

## Execution Sequence

```text
[1] smoke-test-model-routing-preflight
[2] smoke-test-model-routing-lookup
[3] smoke-test-model-routing-execution
[4] smoke-test-model-routing-comparison
[5] smoke-test-model-routing-report
OUTPUT: smoke_test_report + recommendation
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-smoke-test-model-routing.yaml"
  preflight_file: "/tmp/preflight-model-routing.txt"
  lookup_results: []
  comparison_result: {}
  smoke_test_report: {}
```

## Acceptance Criteria

- [ ] o preflight é executado via validator script antes das demais fases
- [ ] os 3 lookups de tier são validados com evidência
- [ ] o teste explícito com `model` e a comparação default são registrados
- [ ] o report final inclui recommendation acionável
- [ ] o wrapper não reimplementa localmente as 5 fases
