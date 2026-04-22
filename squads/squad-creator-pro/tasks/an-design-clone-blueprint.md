<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-design-clone-blueprint
  task_name: Design Clone -- Blueprint
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Assemble Clone Blueprint
    - Estimate Fidelity
    - Emit Integration Rules
  acceptance_criteria:
    - blueprint yaml é gerado
    - fidelity estimate é registrado
    - regras de integração e handoff ficam explícitas
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
  pre_condition: "context_map, stage_plan, trinity e memory_model já existem."
  post_condition: "clone_blueprint final pronto para downstream."
  performance: "não fechar sem blueprint parseável e fidelity estimate."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Design Clone -- Blueprint

## Output Contract

```yaml
output:
  estimated_fidelity: ""
  clone_blueprint:
    mode: ""
    stages: []
    memory: {}
    integration: {}
    estimated_fidelity: ""
```
