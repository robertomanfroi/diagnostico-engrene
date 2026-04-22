---
task-id: update-mind-extract
name: "Process & Extract from New Sources"
version: 1.0.0
execution_type: Agent
model: Sonnet
haiku_eligible: false
estimated-time: 45 min
complexity: medium

inputs:
  required:
    - squad_name: "Nome do squad"
    - agent_slug: "Slug do agent existente"
    - existing_dna: "Parsed DNA from Phase 1"
  optional:
    - new_sources_path: "Caminho para novas fontes"
    - focus: "voice|thinking|both (default: both)"

outputs:
  primary:
    - voice_delta: "New Voice DNA elements extracted"
    - thinking_delta: "New Thinking DNA elements extracted"
    - gap_analysis: "Gaps filled by new sources"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind-extract
  task_name: Process & Extract from New Sources
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 45m
  domain: Operational
  input:
  - '{''squad_name'': ''Nome do squad''}'
  - '{''agent_slug'': ''Slug do agent existente''}'
  - '{''existing_dna'': ''Parsed DNA from Phase 1''}'
  - '{''new_sources_path'': ''Caminho para novas fontes''}'
  - '{''focus'': ''voice|thinking|both (default: both)''}'
  output:
  - '{''voice_delta'': ''New Voice DNA elements extracted''}'
  - '{''thinking_delta'': ''New Thinking DNA elements extracted''}'
  - '{''gap_analysis'': ''Gaps filled by new sources''}'
  action_items:
  - Validate New Sources
  - Identify Gaps Filled
  - Extract Voice DNA Delta
  - Extract Thinking DNA Delta
  acceptance_criteria:
  - New sources validated and classified by tier
  - Voice DNA delta extracted with contradictions identified
  - Thinking DNA delta extracted with contradictions identified
  - Gap analysis documents which gaps are filled and at what confidence
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Process & Extract from New Sources

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `update-mind-extract` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `update-mind` (orchestrator stub)
- **Sequence:** Phase 2 of 4
- **Previous Task:** `update-mind-load`
- **Next Task:** `update-mind-merge`

## Purpose

Processar novas fontes, extrair deltas de Voice DNA e Thinking DNA, e identificar quais gaps do DNA existente as novas fontes preenchem.

## Prerequisites

- Phase 1 completed (existing_dna available)
- New sources provided or identifiable

## Workflow / Steps

### Step 1: Validate New Sources

Execute `collect-sources.md` para novas fontes APENAS:

```yaml
new_sources_validation:
  sources_provided: []
  tier_classification: {}
  adds_to_existing: true|false
  fills_gaps: []
```

### Step 2: Identify Gaps Filled

```yaml
gap_analysis:
  voice_gaps_before:
    - "Faltavam anedotas pessoais"
    - "Tom em situacao X nao documentado"
  thinking_gaps_before:
    - "Heuristica de priorizacao incompleta"
    - "Objection handling nao tinha exemplos"
  gaps_filled_by_new_sources:
    - gap: ""
      source: ""
      confidence: "alta|media|baixa"
```

### Step 3: Extract Voice DNA Delta

Execute `extract-voice-dna.md` nas novas fontes:

```yaml
voice_delta:
  new_power_words: []
  new_signature_phrases: []
  new_stories: []
  new_anti_patterns: []
  new_contradictions: []
  confirms_existing:
    - element: ""
      source_count: "+1"
  contradicts_existing:
    - element: ""
      existing: ""
      new_finding: ""
      resolution: "keep_existing|use_new|flag_for_review"
```

### Step 4: Extract Thinking DNA Delta

Execute `extract-thinking-dna.md` nas novas fontes:

```yaml
thinking_delta:
  new_recognition_patterns: []
  new_heuristics: []
  new_objection_responses: []
  new_handoff_triggers: []
  framework_updates:
    - framework: ""
      change_type: "new_step|clarification|example"
      detail: ""
  contradicts_existing:
    - element: ""
      existing: ""
      new_finding: ""
      resolution: ""
```

## Output

```yaml
voice_delta: { ... }
thinking_delta: { ... }
gap_analysis: { ... }
```

## Acceptance Criteria

- [ ] New sources validated and classified by tier
- [ ] Voice DNA delta extracted with contradictions identified
- [ ] Thinking DNA delta extracted with contradictions identified
- [ ] Gap analysis documents which gaps are filled and at what confidence

## Related Documents

| Document | Relationship |
|----------|-------------|
| `update-mind.md` | Parent orchestrator |
| `update-mind-load.md` | Previous phase |
| `update-mind-merge.md` | Next phase |
| `extract-voice-dna.md` | Delegated extraction |
| `extract-thinking-dna.md` | Delegated extraction |
