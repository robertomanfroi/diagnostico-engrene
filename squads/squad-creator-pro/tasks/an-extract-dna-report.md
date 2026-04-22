<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-dna-report
  task_name: Extract DNA -- Report
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Assemble DNA Report
    - Estimate Fidelity
    - Emit Next Steps
  acceptance_criteria:
    - dna_extraction_report é gerado em YAML
    - fidelity_estimate é registrado com evidência
    - next_steps ficam acionáveis
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
  pre_condition: "source_map, dna_layers, voice_dna e thinking_dna já existem."
  post_condition: "report final pronto para handoff e validação."
  performance: "falhar explicitamente se faltar fidelity_estimate ou next_steps."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Extract DNA -- Report

## Purpose

Montar o `dna_extraction_report` final com prontidão, previews, fidelidade estimada e recomendações de próximo passo.

## Output Contract

```yaml
output:
  fidelity_estimate: ""
  dna_extraction_report:
    sources: {}
    voice_dna_preview: {}
    thinking_dna_preview: {}
    fidelity_estimate: ""
    next_steps: []
```
