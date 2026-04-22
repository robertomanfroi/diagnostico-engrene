<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: smoke-test-model-routing-comparison
  task_name: Smoke Test Model Routing -- Comparison
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Agent
  estimated_time: 5m
  domain: Operational
  action_items:
    - Execute Default Routing Check
    - Compare Explicit vs Default
    - Record Enforcement Gap
  acceptance_criteria:
    - comportamento default é observado
    - comparação com model explícito é registrada
    - enforcement gap ou equivalência é explicitada
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
  pre_condition: "teste explícito já concluído."
  post_condition: "comparação explícito vs default pronta para report."
  performance: "evitar julgamento subjetivo; reportar diferença observável."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Smoke Test Model Routing -- Comparison

## Output Contract

```yaml
output:
  comparison_result:
    explicit_model: "haiku"
    default_model: ""
    behavior_delta: ""
  enforcement_gap: ""
```
