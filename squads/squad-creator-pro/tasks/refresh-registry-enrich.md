---
task-id: refresh-registry-enrich
name: "LLM Enrichment & Build Entries"
version: 1.0.0
execution_type: Agent
model: Haiku
model_rationale: "Semantic inference: domain, keywords, highlights. Haiku sufficient for categorization."
haiku_eligible: true
estimated-time: 10 min
complexity: low

inputs:
  required:
    - script_output: "JSON output from Phase 1"
  optional:
    - preserve_manual: "Keep manual highlights, quality_reference (default: true)"

outputs:
  primary:
    - enriched_entries: "Squad entries with domain, keywords, highlights, example_use"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: refresh-registry-enrich
  task_name: LLM Enrichment & Build Entries
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''script_output'': ''JSON output from Phase 1''}'
  - '{''preserve_manual'': ''Keep manual highlights, quality_reference (default: true)''}'
  output:
  - '{''enriched_entries'': ''Squad entries with domain, keywords, highlights, example_use''}'
  action_items:
  - LLM Enrichment per Squad
  - Build Registry Entry
  - Preserve Manual Annotations
  acceptance_criteria:
  - Domain inferred for each squad
  - 5-15 keywords extracted per squad
  - 2-4 highlights generated per squad
  - Example use generated per squad
  - Manual annotations preserved when applicable
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: LLM Enrichment & Build Entries

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `refresh-registry-enrich` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `refresh-registry` (orchestrator stub)
- **Sequence:** Phase 2 of 3
- **Previous Task:** `refresh-registry-scan`
- **Next Task:** `refresh-registry-write`

## Purpose

For each squad in the script output, apply LLM semantic analysis to infer domain, extract keywords, generate highlights, and create example_use.

## Workflow / Steps

### Step 1: LLM Enrichment per Squad

For each squad in script_output:

1. Read `squads/{name}/README.md` for context

2. **Infer domain** from description + README overview:
   - Categories: content_marketing, technical, business_ops, people_psychology, meta_frameworks
   - Output: Single category that best fits

3. **Extract keywords** from README + agent_names + description:
   - Extract nouns and key phrases
   - Include agent names as keywords
   - Add domain-specific terms
   - Deduplicate and lowercase
   - Output: List of 5-15 keywords

4. **Generate highlights** from README + counts + agent_names:
   - What makes this squad unique?
   - Key features or capabilities
   - Notable agents or frameworks
   - Output: List of 2-4 bullet points

5. **Generate example_use** from purpose + keywords:
   - Create realistic usage example
   - Output: Single sentence starting with verb

### Step 2: Build Registry Entry

For each squad, build entry using template:

```yaml
{squad_name}:
  path: "squads/{squad_name}/"
  domain: "{inferred_domain}"
  purpose: "{description_from_config}"
  keywords: ["{extracted_keywords}"]
  agents: {agent_count}
  tasks: {task_count}
  workflows: {workflow_count}
  highlights:
    - "{highlight_1}"
    - "{highlight_2}"
  example_use: "{generated_example}"
  executor_capable_agents: [...]
  executor_reviewers: [...]
  aggregated_work_contexts: [...]
```

### Step 3: Preserve Manual Annotations

If `preserve_manual: true`, keep existing values for:
- highlights (manual annotations)
- quality_reference
- example_use (if manually set)
- executor_capable_agents (if manually adjusted)

## Output

```yaml
enriched_entries: { all squad entries with semantic data }
```

## Acceptance Criteria

- [ ] Domain inferred for each squad
- [ ] 5-15 keywords extracted per squad
- [ ] 2-4 highlights generated per squad
- [ ] Example use generated per squad
- [ ] Manual annotations preserved when applicable

## Related Documents

| Document | Relationship |
|----------|-------------|
| `refresh-registry.md` | Parent orchestrator |
| `refresh-registry-scan.md` | Previous phase |
| `refresh-registry-write.md` | Next phase |
