<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-design-clone-memory
  task_name: Design Clone -- Memory and Context
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Define Short-Term Memory
    - Define Long-Term Memory
    - Define Context Requirements and Limits
  acceptance_criteria:
    - memória curta e longa são definidas
    - contexto necessário fica explícito
    - limites de memória são documentados
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
  pre_condition: "stages e trinity já estão definidos."
  post_condition: "memory model pronto para blueprint."
  performance: "bloquear se contexto obrigatório não estiver identificado."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Design Clone -- Memory and Context

## Output Contract

```yaml
output:
  memory_model:
    short_term: ""
    long_term: ""
    context_required: []
    limits: []
```
