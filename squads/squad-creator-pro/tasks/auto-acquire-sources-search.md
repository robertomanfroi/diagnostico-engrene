---
task-id: auto-acquire-sources-search
name: "YouTube & Book Mining"
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
    - youtube_sources: "Lista de videos com transcricao"
    - book_sources: "Lista de livros com resumos"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: auto-acquire-sources-search
  task_name: YouTube & Book Mining
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert''}'
  - '{''domain'': ''Area de expertise''}'
  output:
  - '{''youtube_sources'': ''Lista de videos com transcricao''}'
  - '{''book_sources'': ''Lista de livros com resumos''}'
  action_items:
  - YouTube Search Queries
  - YouTube Selection Criteria
  - Catalog YouTube Sources
  - Identify Expert Books
  - Search Book Summaries
  acceptance_criteria:
  - 5+ YouTube videos found with transcript available
  - Expert's main books identified
  - Summary sources cataloged per book
  - Each source has tier classification
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


# Task: YouTube & Book Mining

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-acquire-sources-search` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `auto-acquire-sources` (orchestrator stub)
- **Sequence:** Phase 1 of 3
- **Previous Task:** None
- **Next Task:** `auto-acquire-sources-expand`

## Purpose

Buscar e catalogar fontes do expert no YouTube (interviews, podcasts, keynotes) e identificar livros com resumos disponiveis.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AAS-001 | mind_name and domain must be non-empty | BLOCK |
| VETO-AAS-003 | At least one search tool must be available | BLOCK |

## Workflow / Steps

### Step 1: YouTube Search Queries

Execute these searches:

```
"{mind_name}" interview
"{mind_name}" podcast
"{mind_name}" keynote
"{mind_name}" masterclass
"{mind_name}" talk
"{mind_name}" {domain} advice
```

### Step 2: YouTube Selection Criteria

Prioritize videos that:
- Have 10+ minutes (substantial content)
- Expert is the main interviewee
- Subtitles/transcript available
- High engagement (views, likes)

### Step 3: Catalog YouTube Sources

```yaml
youtube_sources:
  - id: "YT01"
    title: ""
    channel: ""
    duration: ""
    url: ""
    transcript_status: "available|extracted|unavailable"
    tier: 1
    key_topics: []
```

### Step 4: Identify Expert Books

```
"{mind_name}" books
"{mind_name}" author
books by "{mind_name}"
```

### Step 5: Search Book Summaries

For each book found:

```
"{book_title}" summary
"{book_title}" book notes
"{book_title}" key takeaways
"{book_title}" chapter summary
```

Summary sources by quality:

| Source | Tier | Confidence |
|-------|------|-----------|
| Shortform | 2 | Alta (detailed) |
| Blinkist | 2 | Media (condensed) |
| Four Minute Books | 3 | Baixa (very condensed) |
| Blog reviews | 2-3 | Varies |

### Step 6: Catalog Book Sources

```yaml
book_sources:
  - id: "BK01"
    title: ""
    year: ""
    full_book_available: true|false
    summary_sources:
      - source: ""
        url: ""
        depth: "detailed|condensed|highlights"
    tier: 2
```

## Output

```yaml
youtube_sources: [...]
book_sources: [...]
```

## Acceptance Criteria

- [ ] 5+ YouTube videos found with transcript available
- [ ] Expert's main books identified
- [ ] Summary sources cataloged per book
- [ ] Each source has tier classification

## Related Documents

| Document | Relationship |
|----------|-------------|
| `auto-acquire-sources.md` | Parent orchestrator |
| `auto-acquire-sources-expand.md` | Next phase |
