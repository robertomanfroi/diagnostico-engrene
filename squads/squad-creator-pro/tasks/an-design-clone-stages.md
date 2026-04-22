<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-design-clone-stages
  task_name: Design Clone -- Stages
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Decide Single vs Multi-Stage
    - Define Stage Boundaries
    - Validate Structural Freedom
  acceptance_criteria:
    - decisão single vs multi-stage é tomada
    - limites de estágio ficam explícitos
    - rationale estrutural é documentado
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
  pre_condition: "context_map já consolidado."
  post_condition: "stage_plan definido com rationale."
  performance: "evitar multi-stage arbitrário sem diferença comportamental real."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Design Clone -- Stages

## Output Contract

```yaml
output:
  stage_plan:
    mode: "single|multi-stage"
    stages: []
    rationale: ""
```
