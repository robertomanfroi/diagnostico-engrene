---
task-id: auto-acquire-sources
name: "Automated Source Acquisition"
version: 3.0.0
execution_type: Orchestrator
model: Haiku
model_rationale: "Orchestrator stub -- delegates to 3 atomic sub-tasks. Haiku for routing."
haiku_eligible: true
note: "Decomposed from v2.1.0 monolith (363 lines, 5 phases) into 3 atomic tasks."
estimated-time: 15-30 min
complexity: low

workflow_reference: wf-auto-acquire-sources.yaml

inputs:
  required:
    - mind_name: "Nome do expert"
    - domain: "Area de expertise"
  optional:
    - target_count: "Numero alvo de fontes (default: 15)"

outputs:
  primary:
    - acquired_sources: "Lista de fontes adquiridas automaticamente"
    - sources_inventory.yaml: "Inventario estruturado"

tools:
  installed:
    - exa: "Web search"
  recommended:
    - mcp-youtube-transcript: "YouTube transcripts"
    - firecrawl-mcp: "Web scraping"
  see_also: "docs/TOOL-RECOMMENDATIONS.md"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: auto-acquire-sources
  task_name: Automated Source Acquisition
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 15-30m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert''}'
  - '{''domain'': ''Area de expertise''}'
  - '{''target_count'': ''Numero alvo de fontes (default: 15)''}'
  output:
  - '{''acquired_sources'': ''Lista de fontes adquiridas automaticamente''}'
  - '{''sources_inventory.yaml'': ''Inventario estruturado''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 5+ videos YouTube encontrados com transcricao [threshold: >= 5]
  - Livros principais identificados [threshold: >= 1]
  - 3+ podcasts com aparicao do expert [threshold: >= 3]
  - Artigos escritos pelo expert encontrados [threshold: >= 1]
  - Fontes classificadas por tier [threshold: >= 1]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Automated Source Acquisition

> **Principio:** "Maximize o material antes de extrair. Mais fontes = maior fidelidade."
>
> **Modo:** Executa automaticamente, sem input do usuario.

---

## Pipeline (3 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `auto-acquire-sources-search` | YouTube & Book Mining | 10 min |
| 2 | `auto-acquire-sources-expand` | Podcast & Article Mining | 10 min |
| 3 | `auto-acquire-sources-consolidate` | Consolidate, Prioritize & Output | 5 min |

---

## Execution Flow

```
auto-acquire-sources-search
  | youtube_sources, book_sources
  v
auto-acquire-sources-expand
  | podcast_sources, article_sources
  v
auto-acquire-sources-consolidate
  | acquired_sources, sources_inventory.yaml (FINAL OUTPUT)
  v
[DONE]
```

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-AAS-001 | mind_name and domain must be non-empty | Validate inputs before search | VETO - BLOCK |
| VETO-AAS-002 | Target output must not overwrite existing curated sources | Check if sources_inventory.yaml exists | VETO - BLOCK. Prompt for merge/replace. |
| VETO-AAS-003 | At least one search tool must be available | Verify tool availability | VETO - BLOCK |

---

## Integration with collect-sources.md

```yaml
workflow_integration:
  trigger: "collect-sources.md FASE 1"
  mode: "parallel"
  merge_point: "collect-sources.md FASE 2"
```

---

## Quality Check

- [ ] 5+ videos YouTube encontrados com transcricao [threshold: >= 5]
- [ ] Livros principais identificados [threshold: >= 1]
- [ ] 3+ podcasts com aparicao do expert [threshold: >= 3]
- [ ] Artigos escritos pelo expert encontrados [threshold: >= 1]
- [ ] Fontes classificadas por tier [threshold: >= 1]
- [ ] Download queue priorizada [threshold: >= 1]

---

**Squad Architect | Auto-Acquire v3.0**
*"More sources = higher fidelity. Automate the obvious."*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain
- **Outputs:** Lista de fontes adquiridas automaticamente; sources_inventory.yaml: "Inventario estruturado"
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] 5+ videos YouTube encontrados com transcricao [threshold: >= 5]
- [ ] Livros principais identificados [threshold: >= 1]
- [ ] 3+ podcasts com aparicao do expert [threshold: >= 3]
- [ ] Artigos escritos pelo expert encontrados [threshold: >= 1]
- [ ] Fontes classificadas por tier [threshold: >= 1]
- [ ] Download queue priori [threshold: >= 1]
