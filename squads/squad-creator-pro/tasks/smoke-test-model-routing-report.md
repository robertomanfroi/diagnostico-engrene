<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: smoke-test-model-routing-report
  task_name: Smoke Test Model Routing -- Report
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Worker
  estimated_time: 5m
  domain: Operational
  action_items:
    - Aggregate Smoke Evidence
    - Generate Final Report
    - Emit Recommendation
  acceptance_criteria:
    - report final é gerado
    - pelo menos uma entrada de log é referenciada
    - recomendação final é explícita
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
  executor: Worker
  pre_condition: "fases anteriores produziram evidência suficiente."
  post_condition: "smoke test report pronto para decisão."
  performance: "não fechar sem evidência mínima de lookup, execução e comparação."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Smoke Test Model Routing -- Report

## Output Contract

```yaml
output:
  recommendation: ""
  smoke_test_report:
    preflight: ""
    lookups: []
    explicit_execution: {}
    comparison: {}
    recommendation: ""
```
