---
task-id: collect-sources-discover
name: "Discover Sources for Mind Cloning"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Source discovery requires semantic judgment for relevance assessment. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 15 min
complexity: medium

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
  optional:
    - user_materials_path: "Caminho para materiais do usuario (Tier 0)"

outputs:
  primary:
    - discovered_sources: "Lista bruta de fontes descobertas por tipo"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources-discover
  task_name: Discover Sources for Mind Cloning
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''domain'': ''Area de expertise''}'
  - '{''user_materials_path'': ''Caminho para materiais do usuario (Tier 0)''}'
  output:
  - '{''discovered_sources'': ''Lista bruta de fontes descobertas por tipo''}'
  action_items:
  - Validate Inputs
  - Check User Materials (Fallback Chain Step 1)
  - Auto-Acquire Sources (Fallback Chain Step 2)
  - Manual Web Search (Fallback Chain Step 3)
  - 'b: Fail Condition (Fallback Chain Step 4)'
  acceptance_criteria:
  - All required inputs validated before starting discovery [threshold: >= 2 inputs validated]
  - Fallback chain executed in order (user materials -> auto-acquire -> manual search
    -> fail) [threshold: >= 1 chain executed]
  - All 10+ search queries executed for manual search phase [threshold: >= 10]
  - Sources cataloged by type with title, year/date, URL, and relevance [threshold: >= 1 per source]
  - At least 10 raw sources discovered OR fail condition triggered with user notification [threshold: >= 10 sources OR >= 1 fail notification]
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


# Task: Discover Sources for Mind Cloning

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `collect-sources-discover` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `collect-sources` (orchestrator stub)
- **Sequence:** Phase 1 of 5
- **Next Task:** `collect-sources-classify`
- **Specialist:** `@oalanicolas` (DNA Mental source curation methodology)

## Purpose

Execute the initial discovery phase of source collection for mind cloning. Search for all available sources related to the target expert using structured queries, catalog user-provided materials, and apply the fallback chain strategy when sources are insufficient.

## Prerequisites

- `mind_name` and `domain` inputs must be provided and non-empty (VETO-CSR-001)
- If `sources_inventory` file already exists at target path, back it up before proceeding (VETO-CSR-002)

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `mind_name` | Yes | Nome do expert a clonar |
| `domain` | Yes | Area de expertise |
| `user_materials_path` | No | Caminho para materiais do usuario (Tier 0) |

## Workflow / Steps

### Step 1: Validate Inputs

Confirm `mind_name` and `domain` are provided and non-empty. If not, VETO-BLOCK and request valid inputs.

### Step 2: Check User Materials (Fallback Chain Step 1)

```
Pergunta ao usuario:
"Voce possui materiais proprios do expert {mind_name}?
(livros, PDFs, transcricoes, notas de aula, etc.)"

├── SIM → Indexar como Tier 0 (maxima confianca)
│         Prosseguir para complementar com web
└── NAO → Ir para Step 3
```

If user provides materials path:
- Catalog each file with type, format, estimated volume
- Tag all as Tier 0 (direct from expert, maximum confidence)

### Step 3: Auto-Acquire Sources (Fallback Chain Step 2)

Execute `auto-acquire-sources.md` task for automated search:
- YouTube transcripts
- Book summaries
- Podcast appearances
- Articles/blogs

Check result: `total_sources >= 10?`
- SIM: Proceed to Step 5
- NAO: Continue to Step 4

### Step 4: Manual Web Search (Fallback Chain Step 3)

Execute ALL these search queries:

```
# Conteudo Primario (do proprio expert)
"{nome}" books
"{nome}" interview transcript
"{nome}" podcast appearance
"{nome}" keynote speech
"{nome}" masterclass
"{nome}" framework methodology

# Conteudo Secundario (sobre o expert)
"{nome}" biography
"{nome}" case study
"{nome}" best quotes
"{nome}" principles philosophy
```

Check result: `total_sources >= 10?`
- SIM: Proceed to Step 5
- NAO: Continue to Fail condition

### Step 4b: Fail Condition (Fallback Chain Step 4)

If `total_sources < 5`: HALT workflow. Notify user: "Fontes insuficientes para {mind_name}. Minimo: 10 fontes (5 Tier 1). Opcoes: (1) fornecer materiais proprios, (2) escolher outro expert, (3) prosseguir com qualidade reduzida." Await user decision.

### Step 5: Catalog Discovered Sources

Organize all discovered sources by type:

```yaml
discovered_sources:
  books:
    - title: ""
      year: ""
      relevance: "alta|media"
      status: "disponivel|indisponivel"

  interviews_podcasts:
    - title: ""
      host: ""
      duration: ""
      url: ""

  articles_posts:
    - title: ""
      source: ""
      url: ""

  videos_talks:
    - title: ""
      event: ""
      duration: ""
      url: ""

  courses_workshops:
    - title: ""
      platform: ""
      url: ""
```

## Output

```yaml
discovered_sources:
  user_materials_count: 0
  auto_acquired_count: 0
  manual_search_count: 0
  total_raw_sources: 0
  sources_by_type:
    books: []
    interviews_podcasts: []
    articles_posts: []
    videos_talks: []
    courses_workshops: []
```

## Acceptance Criteria

- [ ] All required inputs validated before starting discovery [threshold: >= 2 inputs validated]
- [ ] Fallback chain executed in order (user materials -> auto-acquire -> manual search -> fail) [threshold: >= 1 chain executed]
- [ ] All 10+ search queries executed for manual search phase [threshold: >= 10]
- [ ] Sources cataloged by type with title, year/date, URL, and relevance [threshold: >= 1 per source]
- [ ] At least 10 raw sources discovered OR fail condition triggered with user notification [threshold: >= 10 sources OR >= 1 fail notification]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CSR-001 | `mind_name` and `domain` must be provided and non-empty | Validate required inputs before starting discovery | VETO - BLOCK. Reject execution and request valid inputs. |
| VETO-CSR-002 | Existing `sources_inventory` must be backed up before overwrite | Check if `sources_inventory` file already exists at target path | VETO - BLOCK. Create backup before proceeding. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `collect-sources.md` | Parent orchestrator |
| `collect-sources-classify.md` | Next phase (Tier classification) |
| `auto-acquire-sources.md` | Sub-task for automated source acquisition |
