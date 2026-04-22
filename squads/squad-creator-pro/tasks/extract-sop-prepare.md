---
task-id: extract-sop-prepare
name: "Fetch Transcript & Preparation"
version: 1.0.0
execution_type: Hybrid
model: Opus
haiku_eligible: false
estimated-time: 15 min
complexity: low

inputs:
  required:
    - transcript: "Meeting transcript (text, audio, or video transcript)"
  optional:
    - domain_context: "Business domain for terminology context"
    - existing_docs: "Current SOPs, manuals, or process docs"
    - process_owner: "Who to validate extracted SOP with"

outputs:
  primary:
    - transcript_object: "Standardized transcript with metadata"
    - preparation_notes: "Language, speakers, chunks identified"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-sop-prepare
  task_name: Fetch Transcript & Preparation
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Operational
  input:
  - '{''transcript'': ''Meeting transcript (text, audio, or video transcript)''}'
  - '{''domain_context'': ''Business domain for terminology context''}'
  - '{''existing_docs'': ''Current SOPs, manuals, or process docs''}'
  - '{''process_owner'': ''Who to validate extracted SOP with''}'
  output:
  - '{''transcript_object'': ''Standardized transcript with metadata''}'
  - '{''preparation_notes'': ''Language, speakers, chunks identified''}'
  action_items:
  - Fetch Transcript (Data Source Resolution)
  - Standardize Transcript Object
  - Prepare for Extraction
  acceptance_criteria:
  - Transcript fetched and non-empty
  - Language identified
  - Speakers/process explainer identified
  - Chunking applied if needed
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


# Task: Fetch Transcript & Preparation

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-sop-prepare` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `extract-sop` (orchestrator stub)
- **Sequence:** Phase 1 of 4
- **Previous Task:** None
- **Next Task:** `extract-sop-extract`

## Purpose

Fetch transcript from configured data source, validate, normalize, and prepare for extraction passes.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-ESP-001 | Transcript must be non-empty | BLOCK - Resolve data source and retry |

## Workflow / Steps

### Step 1: Fetch Transcript (Data Source Resolution)

1. Load configuration from `config/squad-config.yaml`
2. Read `data_sources.transcripts.active_source`
3. Fetch based on source type:

```yaml
if active_source == "supabase":
  - Connect using env vars
  - Execute query from config
  - Map fields
elif active_source == "local_file":
  - Read from base_path
  - Parse based on extension
elif active_source == "api":
  - Call endpoint
  - Parse response
elif active_source == "direct":
  - Use transcript passed as input parameter
```

**Elicit if source not configured:**
```
Which transcript source should I use?
1. Supabase database (default)
2. Local file (provide path)
3. External API (requires config)
4. Direct input (paste transcript)
```

### Step 2: Standardize Transcript Object

```yaml
transcript:
  transcript_id: string
  transcript_content: string
  transcript_source: string
  transcript_url: string
  transcript_duration: number
  transcript_participants: array
  transcript_date: date
  transcript_language: string
  transcript_metadata: object
```

### Step 3: Prepare for Extraction

1. Validate transcript was fetched successfully
2. Identify language and normalize if needed
3. Mark timestamps or speaker changes
4. Identify main process explainer
5. Apply chunking if transcript exceeds `max_tokens_per_chunk`

**Elicit if unclear:**
```
What is the business domain of this process?
Who is the process owner to validate with?
Are there existing documents to cross-reference?
```

## Output

```yaml
transcript_object: { standardized transcript }
preparation_notes:
  language: ""
  speakers: []
  main_explainer: ""
  chunks: 0
  domain_context: ""
```

## Acceptance Criteria

- [ ] Transcript fetched and non-empty
- [ ] Language identified
- [ ] Speakers/process explainer identified
- [ ] Chunking applied if needed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-sop.md` | Parent orchestrator |
| `extract-sop-extract.md` | Next phase |
| `config/squad-config.yaml` | Data source configuration |
