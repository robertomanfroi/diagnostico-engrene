---
task-id: update-mind-apply
name: "Apply Updates & Generate Diff Report"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
haiku_eligible: false
estimated-time: 15 min
complexity: low

inputs:
  required:
    - squad_name: "Nome do squad"
    - agent_slug: "Slug do agent"
    - merge_plan: "Merge plan from Phase 3"
    - snapshot_before: "Snapshot from Phase 1"

outputs:
  primary:
    - updated_agent: "Agent file atualizado com novo DNA"
    - diff_report: "Complete update report with before/after comparison"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind-apply
  task_name: Apply Updates & Generate Diff Report
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Operational
  input:
  - '{''squad_name'': ''Nome do squad''}'
  - '{''agent_slug'': ''Slug do agent''}'
  - '{''merge_plan'': ''Merge plan from Phase 3''}'
  - '{''snapshot_before'': ''Snapshot from Phase 1''}'
  output:
  - '{''updated_agent'': ''Agent file atualizado com novo DNA''}'
  - '{''diff_report'': ''Complete update report with before/after comparison''}'
  action_items:
  - Apply Merge Plan to Agent File
  - Update Metadata
  - Generate Snapshot After
  - Generate Diff Report
  acceptance_criteria:
  - Agent file updated with merge plan applied
  - Snapshot "after" generated with accurate counts
  - Diff report shows before/after comparison
  - Quality impact calculated
  - Files modified and backup paths documented
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Apply Updates & Generate Diff Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `update-mind-apply` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `update-mind` (orchestrator stub)
- **Sequence:** Phase 4 of 4
- **Previous Task:** `update-mind-merge`
- **Next Task:** None (final phase)

## Purpose

Aplicar o merge plan no agent file, gerar snapshot "after", calcular diff report com impacto em quality scores.

## Prerequisites

- Phase 3 completed (merge_plan available)
- Backup exists from Phase 1

## Workflow / Steps

### Step 1: Apply Merge Plan to Agent File

```yaml
agent_update:
  agent_path: "squads/{squad_name}/agents/{agent_slug}.md"
  sections_to_regenerate:
    - "voice_dna block"
    - "thinking_dna block"
  preserve:
    - "Custom instructions"
    - "Squad-specific config"
    - "Handoff rules"
```

### Step 2: Update Metadata

```yaml
metadata_update:
  path: "squads/{squad_name}/minds/{agent_slug}/metadata.yaml"
  new_sources_added: 0
```

### Step 3: Generate Snapshot After

```yaml
snapshot_after:
  voice_dna:
    power_words_count: 0
    signature_phrases_count: 0
    stories_count: 0
    anti_patterns_count: 0
  thinking_dna:
    frameworks_count: 0
    heuristics_count: 0
    recognition_patterns_count: 0
  sources:
    total: 0
    tier_1: 0
```

### Step 4: Generate Diff Report

```yaml
update_report:
  metadata:
    mind_name: ""
    mind_slug: ""
    update_date: ""
    mode: ""
    new_sources_processed: 0
  changes:
    voice_dna:
      added: []
      updated: []
      unchanged: []
    thinking_dna:
      added: []
      updated: []
      unchanged: []
  quality:
    before:
      voice_score: ""
      thinking_score: ""
      fidelity: ""
    after:
      voice_score: ""
      thinking_score: ""
      fidelity: ""
    improvement: "+X%"
  files:
    updated:
      - path: ""
        changes: ""
    backed_up:
      - original: ""
        backup: ""
  next_steps:
    - "Regenerar agent.md se qualidade aumentou significativamente"
    - "Rodar smoke tests para validar mudancas"
    - "Atualizar squad config se necessario"
```

## Output

```yaml
updated_agent: "squads/{squad_name}/agents/{agent_slug}.md"
diff_report: { update_report as above }
```

## Acceptance Criteria

- [ ] Agent file updated with merge plan applied
- [ ] Snapshot "after" generated with accurate counts
- [ ] Diff report shows before/after comparison
- [ ] Quality impact calculated
- [ ] Files modified and backup paths documented
- [ ] Next steps listed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `update-mind.md` | Parent orchestrator |
| `update-mind-merge.md` | Previous phase |
