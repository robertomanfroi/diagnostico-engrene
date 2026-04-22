<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: smoke-test-model-routing-preflight
  task_name: Smoke Test Model Routing -- Preflight
  status: pending
  responsible_executor: '@pedro-valerio'
  execution_type: Worker
  estimated_time: 5m
  domain: Operational
  action_items:
    - Run Validator Script
    - Verify Metrics Path
    - Confirm Logger Availability
  acceptance_criteria:
    - preflight validator executa com sucesso
    - metrics path está disponível para escrita
    - logger script está acessível
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
  pre_condition: "config e scripts do routing existem."
  post_condition: "preflight artifact pronto para fases seguintes."
  performance: "bloquear o smoke test se o validator falhar."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Smoke Test Model Routing -- Preflight

## Output Contract

```yaml
output:
  preflight_file: "/tmp/preflight-model-routing.txt"
  config_ready: true
  metrics_ready: true
  logger_ready: true
```
