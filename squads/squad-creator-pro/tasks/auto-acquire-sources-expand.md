---
task-id: auto-acquire-sources-expand
name: "Podcast & Article Mining"
version: 1.0.0
execution_type: Hybrid
model: Haiku
model_rationale: "Web search + fetch are deterministic. LLM only formats results."
haiku_eligible: true
estimated-time: 10 min
complexity: low

inputs:
  required:
    - mind_name: "Nome do expert"
    - domain: "Area de expertise"

outputs:
  primary:
    - podcast_sources: "Lista de episodios com aparicao do expert"
    - article_sources: "Lista de artigos escritos pelo/sobre o expert"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: auto-acquire-sources-expand
  task_name: Podcast & Article Mining
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert''}'
  - '{''domain'': ''Area de expertise''}'
  output:
  - '{''podcast_sources'': ''Lista de episodios com aparicao do expert''}'
  - '{''article_sources'': ''Lista de artigos escritos pelo/sobre o expert''}'
  action_items:
  - Podcast Search Queries
  - Catalog Podcast Sources
  - Article Search - By Expert
  - Article Search - About Expert
  - Catalog Article Sources
  acceptance_criteria:
  - 3+ podcasts with expert appearance found
  - Articles written BY expert identified
  - Articles written ABOUT expert identified
  - Tier classification applied (1 for expert's own, 2 for about)
  - Transcript availability noted for podcasts
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Podcast & Article Mining

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-acquire-sources-expand` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `auto-acquire-sources` (orchestrator stub)
- **Sequence:** Phase 2 of 3
- **Previous Task:** `auto-acquire-sources-search`
- **Next Task:** `auto-acquire-sources-consolidate`

## Purpose

Buscar e catalogar aparicoes do expert em podcasts e artigos/blogs escritos pelo ou sobre o expert.

## Workflow / Steps

### Step 1: Podcast Search Queries

```
"{mind_name}" podcast guest
"{mind_name}" appeared on
"{mind_name}" interview episode
site:spotify.com "{mind_name}"
site:podcasts.apple.com "{mind_name}"
```

### Step 2: Catalog Podcast Sources

```yaml
podcast_sources:
  - id: "PD01"
    show_name: ""
    episode_title: ""
    host: ""
    duration: ""
    url: ""
    transcript_available: true|false
    tier: 1
```

### Step 3: Article Search - By Expert

```
"{mind_name}" blog
"{mind_name}" newsletter
"{mind_name}" articles
site:medium.com "{mind_name}"
site:linkedin.com/pulse "{mind_name}"
```

### Step 4: Article Search - About Expert

```
"{mind_name}" methodology
"{mind_name}" framework explained
"{mind_name}" principles
"{mind_name}" biography
```

### Step 5: Catalog Article Sources

```yaml
article_sources:
  - id: "AR01"
    title: ""
    author: ""
    source: ""
    url: ""
    tier: 1|2  # 1 if author is the expert, 2 if about the expert
```

## Output

```yaml
podcast_sources: [...]
article_sources: [...]
```

## Acceptance Criteria

- [ ] 3+ podcasts with expert appearance found
- [ ] Articles written BY expert identified
- [ ] Articles written ABOUT expert identified
- [ ] Tier classification applied (1 for expert's own, 2 for about)
- [ ] Transcript availability noted for podcasts

## Related Documents

| Document | Relationship |
|----------|-------------|
| `auto-acquire-sources.md` | Parent orchestrator |
| `auto-acquire-sources-search.md` | Previous phase |
| `auto-acquire-sources-consolidate.md` | Next phase |
