---
task-id: update-mind-load-snapshot
name: "Load Existing DNA & Create Snapshot"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
haiku_eligible: false
estimated-time: 10 min
complexity: low

inputs:
  required:
    - squad_name: "Nome do squad (ex: copy, legal)"
    - agent_slug: "Slug do agent existente (snake_case)"
  optional:
    - focus: "voice|thinking|both (default: both)"

outputs:
  primary:
    - snapshot_before: "Snapshot YAML com contagens e scores do DNA atual"
    - existing_files: "Mapa de arquivos existentes do agent"
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind-load-snapshot
  task_name: Load Existing DNA & Create Snapshot
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''squad_name'': ''Nome do squad (ex: copy, legal)''}'
  - '{''agent_slug'': ''Slug do agent existente (snake_case)''}'
  - '{''focus'': ''voice|thinking|both (default: both)''}'
  output:
  - '{''snapshot_before'': ''Snapshot YAML com contagens e scores do DNA atual''}'
  - '{''existing_files'': ''Mapa de arquivos existentes do agent''}'
  action_items:
  - Locate Existing Files
  - Create Backup
  - Generate Snapshot Before
  acceptance_criteria:
  - Agent file located and validated as parseable
  - Backup created at `.backup/` before any modification
  - Snapshot counts are accurate (verified against file content)
  - All existing file paths mapped
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


# Task: Load Existing DNA & Create Snapshot

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `update-mind-load-snapshot` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `update-mind` (orchestrator stub)
- **Sequence:** Phase 1 of 3
- **Previous Task:** None
- **Next Task:** `update-mind-extract-merge`

## Purpose

Localizar arquivos existentes do agent, criar backup de seguranca, e gerar snapshot quantitativo do DNA atual para comparacao posterior (diff report).

## Prerequisites

- Agent existente em `squads/{squad_name}/agents/{agent_slug}.md`
- Squad valido no ecossistema

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `squad_name` | Yes | Nome do squad |
| `agent_slug` | Yes | Slug do agent existente |
| `focus` | No | voice, thinking ou both (default: both) |

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-UPM-001 | Agent file must exist and be parseable | BLOCK - Fix path or structure before proceeding |
| VETO-UPM-002 | Backup must be created before any modification | BLOCK - Create backup snapshot first |

## Workflow / Steps

### Step 1: Locate Existing Files

```yaml
existing_files:
  agent_file: "squads/{squad_name}/agents/{agent_slug}.md"
  sources_dir: "squads/{squad_name}/minds/{agent_slug}/sources/"
  metadata: "squads/{squad_name}/minds/{agent_slug}/metadata.yaml"
```

Validate each file exists. Agent file is REQUIRED; sources_dir and metadata are optional.

### Step 2: Create Backup

```yaml
backup:
  path: "squads/{squad_name}/.backup/{agent_slug}.{timestamp}.md"
  action: "Copy current agent file to backup location"
```

### Step 3: Generate Snapshot Before

```yaml
snapshot_before:
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
  quality_scores:
    voice: "X/10"
    thinking: "X/9"
    fidelity_estimate: "X%"
```

Count each element by parsing the existing agent file YAML blocks.

## Output

```yaml
snapshot_before: { ... }
existing_files: { ... }
backup_path: "squads/{squad_name}/.backup/{agent_slug}.{timestamp}.md"
```

## Acceptance Criteria

- [ ] Agent file located and validated as parseable
- [ ] Backup created at `.backup/` before any modification
- [ ] Snapshot counts are accurate (verified against file content)
- [ ] All existing file paths mapped

## Related Documents

| Document | Relationship |
|----------|-------------|
| `update-mind.md` | Parent orchestrator |
| `update-mind-extract-merge.md` | Next phase |
