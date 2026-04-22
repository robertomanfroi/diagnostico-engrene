<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-dna-voice-dna
  task_name: Extract DNA -- Voice DNA
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  action_items:
    - Define Identity Statement
    - Capture Vocabulary and Signature Phrases
    - Score Tone and Storytelling
  acceptance_criteria:
    - identity statement é definido
    - power words e signature phrases são documentadas
    - tone dimensions e storytelling patterns ficam explícitos
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
  pre_condition: "camadas e evidências de comunicação já extraídas."
  post_condition: "voice_dna documentado com linguagem reutilizável."
  performance: "evitar generalidades; preservar marca verbal do mind."
```
<!-- SINKRA_CONTRACT:END -->

# Task: Extract DNA -- Voice DNA

## Purpose

Consolidar a camada verbal do mind em um bloco reutilizável para clone, prompts e validação posterior.

## Output Contract

```yaml
output:
  voice_dna:
    identity: ""
    power_words: []
    signature_phrases: []
    tone: {}
    storytelling_patterns: []
```
