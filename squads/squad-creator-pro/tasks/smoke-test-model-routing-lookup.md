<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: smoke-test-model-routing-lookup
  task_name: Smoke Test Model Routing -- Lookup
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Worker
  estimated_time: 5m
  domain: Operational
  action_items:
    - Validate Tier Lookup
    - Compare Expected vs Actual
    - Record Lookup Evidence
  acceptance_criteria:
    - 3 lookups retornam tier esperado
    - divergências ficam registradas
    - evidence bundle é produzido
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
  pre_condition: "preflight do routing já passou."
  post_condition: "lookup evidence pronto para execução."
  performance: "falhar explicitamente se o tier esperado divergir."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Smoke Test Model Routing -- Lookup

## Output Contract

```yaml
output:
  lookup_results:
    - task: ""
      expected_tier: ""
      actual_tier: ""
  lookup_passed: true
```
