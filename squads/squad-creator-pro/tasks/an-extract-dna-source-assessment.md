<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-dna-source-assessment
  task_name: Extract DNA -- Source Assessment
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Inventory Sources
    - Classify Gold vs Bronze
    - Score Curation Readiness
  acceptance_criteria:
    - todas as fontes relevantes são inventariadas
    - ouro vs bronze é classificado com evidência
    - source_map e curadoria_score são produzidos
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
  pre_condition: "fontes e contexto mínimo do mind resolvidos."
  post_condition: "source_map e curadoria_score prontos para extração."
  performance: "bloquear extração se a cobertura mínima não existir."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Extract DNA -- Source Assessment

## Purpose

Classificar as fontes do mind em ouro vs bronze, medir prontidão e bloquear a extração se a base estiver fraca.

## Output Contract

```yaml
output:
  source_map:
    ouro: []
    bronze: []
  curadoria_score: 0
  extraction_ready: true
  quality_assessment: ""
```
