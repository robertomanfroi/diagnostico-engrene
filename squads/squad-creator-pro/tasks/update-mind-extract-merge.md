---
task-id: update-mind-extract-merge
name: "Extract Deltas & Merge Strategy"
version: 1.0.0
execution_type: Agent
model: Sonnet
haiku_eligible: false
estimated-time: 50 min
complexity: medium

inputs:
  required:
    - squad_name: "Nome do squad"
    - agent_slug: "Slug do agent existente"
    - snapshot_before: "Snapshot do Phase 1"
    - existing_files: "Mapa de arquivos do Phase 1"
  optional:
    - new_sources_path: "Caminho para novas fontes"
    - focus: "voice|thinking|both (default: both)"
    - mode: "merge|replace|selective"

outputs:
  primary:
    - voice_delta: "Novos elementos de Voice DNA extraidos"
    - thinking_delta: "Novos elementos de Thinking DNA extraidos"
    - merge_plan: "Plano de merge com conflitos resolvidos"
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind-extract-merge
  task_name: Extract Deltas & Merge Strategy
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 50m
  domain: Strategic
  input:
  - '{''squad_name'': ''Nome do squad''}'
  - '{''agent_slug'': ''Slug do agent existente''}'
  - '{''snapshot_before'': ''Snapshot do Phase 1''}'
  - '{''existing_files'': ''Mapa de arquivos do Phase 1''}'
  - '{''new_sources_path'': ''Caminho para novas fontes''}'
  output:
  - '{''voice_delta'': ''Novos elementos de Voice DNA extraidos''}'
  - '{''thinking_delta'': ''Novos elementos de Thinking DNA extraidos''}'
  - '{''merge_plan'': ''Plano de merge com conflitos resolvidos''}'
  action_items:
  - Validate New Sources
  - Identify Gaps Filled
  - Extract Voice DNA Delta
  - Extract Thinking DNA Delta
  - Define Merge Strategy
  acceptance_criteria:
  - New sources validated and classified
  - Voice DNA delta extracted with contradictions identified
  - Thinking DNA delta extracted with contradictions identified
  - Merge strategy defined per mode
  - All conflicts documented with recommendation
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


# Task: Extract Deltas & Merge Strategy

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `update-mind-extract-merge` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `update-mind` (orchestrator stub)
- **Sequence:** Phase 2 of 3
- **Previous Task:** `update-mind-load-snapshot`
- **Next Task:** `update-mind-apply`

## Purpose

Processar novas fontes, extrair deltas de Voice DNA e Thinking DNA, identificar conflitos com DNA existente, e definir estrategia de merge.

## Prerequisites

- Phase 1 completed (snapshot_before and existing_files available)
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
  voice_gaps_before: []
  thinking_gaps_before: []
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

### Step 5: Define Merge Strategy

| Mode | Behavior |
|------|----------|
| **merge** | Add new elements, preserve existing |
| **replace** | Replace sections where new is significantly better |
| **selective** | Checkpoint per section, user decides |

```yaml
merge_rules:
  additive:
    - power_words
    - signature_phrases
    - stories
    - heuristics
    - recognition_patterns
  protected:
    - primary_framework
    - identity_statement
    - veto_heuristics
  replace_if_better:
    - diagnostic_questions
    - objection_responses
    - decision_pipeline
```

### Step 6: Resolve Conflicts

```yaml
conflicts:
  - section: ""
    existing_value: ""
    new_value: ""
    recommendation: "keep|replace|merge"
    rationale: ""
  resolution_strategy:
    auto_resolve:
      - "New element does not exist in current -> ADD"
      - "Same element with more details -> ENRICH"
      - "Same element with additional examples -> ADD EXAMPLES"
    require_human:
      - "Direct contradiction in framework"
      - "Change in identity_statement"
      - "Removal of existing element"
```

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-UPM-003 | Protected sections must not be replaced without human approval | BLOCK - Route through selective mode |

## Output

```yaml
voice_delta: { ... }
thinking_delta: { ... }
merge_plan:
  mode: "merge|replace|selective"
  conflicts: []
  auto_resolved: []
  requires_human: []
```

## Acceptance Criteria

- [ ] New sources validated and classified
- [ ] Voice DNA delta extracted with contradictions identified
- [ ] Thinking DNA delta extracted with contradictions identified
- [ ] Merge strategy defined per mode
- [ ] All conflicts documented with recommendation
- [ ] Protected sections flagged if changes proposed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `update-mind.md` | Parent orchestrator |
| `update-mind-load-snapshot.md` | Previous phase |
| `update-mind-apply.md` | Next phase |
| `extract-voice-dna.md` | Delegated extraction |
| `extract-thinking-dna.md` | Delegated extraction |
