<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-dna-layer-extraction
  task_name: Extract DNA -- Layer Extraction
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 15m
  domain: Operational
  action_items:
    - Extract 8 Layers
    - Capture Frameworks and Heuristics
    - Record Evidence per Layer
  acceptance_criteria:
    - 8 camadas são mapeadas
    - cada camada inclui evidência de fonte
    - frameworks SE/ENTAO ficam explícitos
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
  pre_condition: "source_map validado e pronto para extração."
  post_condition: "8 camadas do DNA mental extraídas com evidência."
  performance: "não aceitar descrição superficial sem framework implícito."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Extract DNA -- Layer Extraction

## Purpose

Extrair as 8 camadas do DNA mental a partir das fontes ouro, com heurísticas, valores, obsessões e paradoxos apoiados por evidência.

## Output Contract

```yaml
output:
  dna_layers:
    - layer: "behavioral_patterns"
      evidence: []
      framework: ""
  layer_coverage: 8
  extraction_notes: []
```
