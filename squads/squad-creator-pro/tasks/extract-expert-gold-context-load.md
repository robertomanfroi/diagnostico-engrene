---
task-id: extract-expert-gold-context-load
name: "Context Load — Expert Knowledge Baseline"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Scanning existing references and selecting analysts requires contextual reasoning."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - source_file: "Path to transcription file (.md or .txt, preferably diarized)"
    - expert_slug: "Expert identifier (e.g., thiagoroas, russellbrunson)"
    - expert_name: "Human-readable name (e.g., Thiago Roas)"
    - target_squads: "Squads to enrich (e.g., [copy, traffic-masters])"
  optional:
    - analyst_agents: "Override default analyst selection per squad"
    - source_context: "Description of source (e.g., Podcast Segredos da Escala #122, 3h01m)"

outputs:
  primary:
    - existing_knowledge: "Baseline of what we already know about this expert"
    - selected_analysts: "Confirmed list of analyst agents to dispatch"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold-context-load
  task_name: Context Load — Expert Knowledge Baseline
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''source_file'': ''Path to transcription file (.md or .txt, preferably diarized)''}'
  - '{''expert_slug'': ''Expert identifier (e.g., thiagoroas, russellbrunson)''}'
  - '{''expert_name'': ''Human-readable name (e.g., Thiago Roas)''}'
  - '{''target_squads'': ''Squads to enrich (e.g., [copy, traffic-masters])''}'
  - '{''analyst_agents'': ''Override default analyst selection per squad''}'
  output:
  - '{''existing_knowledge'': ''Baseline of what we already know about this expert''}'
  - '{''selected_analysts'': ''Confirmed list of analyst agents to dispatch''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Baseline of what we already know about this expert'
  - Task output validated against quality standards
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


# Task: Context Load -- Expert Knowledge Baseline

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-expert-gold-context-load` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `extract-expert-gold` (orchestrator stub)
- **Sequence:** Phase 1 of 5
- **Next Task:** `extract-expert-gold-multi-lense`

## Purpose

Build a knowledge baseline of what we already know about the target expert before extraction begins. Scan existing reference files across target squads, count documented insights and frameworks, then select the analyst agents that will perform multi-lense extraction.

## Prerequisites

- `source_file` must exist and be readable
- `expert_slug` must be non-empty
- `target_squads` must contain at least one valid squad name

## Step 0.1: Scan Existing References

```yaml
search_paths:
  - squads/{squad}/data/references/{expert_slug}-*.yaml
  - squads/{squad}/data/references/{expert_slug}-*.md
  - squads/{squad}/data/sops/*{expert_slug}*
  - docs/research/{expert_slug}-*.md

for each file found:
  - Record: path, line_count, last_modified
  - Extract: section headers, key topics covered
  - Count: existing insights/frameworks
```

## Step 0.2: Build Knowledge Baseline

```yaml
output:
  existing_knowledge:
    files: [{path, lines, topics}]
    total_insights: N
    frameworks_documented: []
    gaps_known: []
  new_source:
    file: "{source_file}"
    format: "diarized_md | raw_txt | json"
    estimated_duration: "Xh Ym"
    word_count: N
```

## Step 0.3: Select Analyst Agents

If `analyst_agents` not provided, select based on `target_squads`:

```yaml
default_analysts:
  copy:
    - eugene-schwartz    # Awareness levels, sophistication
    - jon-benson         # VSL structure, format, production
    - dan-kennedy        # Monetization, metrics, direct response
    - todd-brown         # Unique mechanisms, big ideas
  traffic-masters:
    - depesh-mandalia    # Strategic Meta Ads, brand + DR
    - ralph-burns        # Scaling, creative testing
    - kasim-aslam        # Google Ads, Performance Max
    - pedro-sobral       # Brazil market, operational execution
  hormozi:
    - hormozi-offers     # Offer architecture, value equation
    - hormozi-models     # Money models, unit economics
    - hormozi-leads      # Lead generation, core four
  storytelling:
    - joseph-campbell    # Narrative structure, archetypes
    - kindra-hall        # Business storytelling
    - park-howell        # ABT framework, brand narrative
```

## Elicitation Point

**Checkpoint:** Confirm analyst selection with user before proceeding.

Present the selected analysts and ask:
> "These are the analysts I'll use for extraction. Confirm or override?"

**Default:** Use defaults per squad.

## Output

Pass `existing_knowledge` and `selected_analysts` to the next task (`extract-expert-gold-multi-lense`).

---

_Task Version: 1.0.0_
_Parent: extract-expert-gold_
_Phase: 0 -- Context Load_

## Acceptance Criteria

- [ ] Output artifact produced: Baseline of what we already know about this expert
- [ ] Task output validated against quality standards
