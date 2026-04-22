---
task-id: extract-expert-gold
name: "Extract Expert Gold (Knowledge Enrichment Pipeline)"
version: 2.0.0
execution_type: Orchestrator
model: Sonnet
model_rationale: "Orchestrator stub -- delegates to atomic sub-tasks. Sonnet for routing decisions."
haiku_eligible: false
note: "Decomposed from v1.0.0 monolith (461 lines) into 5 atomic tasks."
estimated-time: 60-90 min
complexity: high

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
    - enriched_references: "Updated squad reference files with new insights"
    - extraction_report: "Full summary with stats, conflicts, gaps"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-expert-gold
  task_name: Extract Expert Gold (Knowledge Enrichment Pipeline)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 60-90m
  domain: Operational
  input:
  - '{''source_file'': ''Path to transcription file (.md or .txt, preferably diarized)''}'
  - '{''expert_slug'': ''Expert identifier (e.g., thiagoroas, russellbrunson)''}'
  - '{''expert_name'': ''Human-readable name (e.g., Thiago Roas)''}'
  - '{''target_squads'': ''Squads to enrich (e.g., [copy, traffic-masters])''}'
  - '{''analyst_agents'': ''Override default analyst selection per squad''}'
  output:
  - '{''enriched_references'': ''Updated squad reference files with new insights''}'
  - '{''extraction_report'': ''Full summary with stats, conflicts, gaps''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 'Output artifact produced: Updated squad reference files with new insights'
  - Task output validated against quality standards
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


# Extract Expert Gold (Knowledge Enrichment Pipeline)

> "Raw content is noise. Extracted frameworks are signal."

## Pipeline (5 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 0 | `extract-expert-gold-context-load` | Context Load | 10 min |
| 1 | `extract-expert-gold-multi-lense` | Multi-Lense Extraction | 20 min |
| 2 | `extract-expert-gold-filter` | Gold Filter | 15 min |
| 3 | `extract-expert-gold-enrichment` | Enrichment | 15 min |
| 4 | `extract-expert-gold-validation` | Validation | 10 min |

---

## Execution Flow

```
extract-expert-gold-context-load
  | existing_knowledge, selected_analysts
  v
extract-expert-gold-multi-lense
  | merged_extraction
  v
extract-expert-gold-filter
  | gold_summary, classified_insights
  v
extract-expert-gold-enrichment
  | enriched_files
  v
extract-expert-gold-validation
  | extraction_report, validation_result
  v
[DONE]
```

---

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-extract-expert-gold.yaml`

---

## Elicitation Points (Consolidated)

| # | Phase | When | Question | Default |
|---|-------|------|----------|---------|
| 1 | 0 | Analyst selection | "These are the analysts I'll use. Confirm or override?" | Use defaults per squad |
| 2 | 2 | Gold summary ready | "Here's the gold summary. Proceed with enrichment?" | Yes |
| 3 | 3 | Conflicts found | "Found contradictions. Which version to keep?" | Flag both |

---

## Quality Gate

```yaml
gate_id: SC_EEG_001
gate_name: "Expert Gold Extraction Quality"
checks:
  - "Phase 0 baseline documented"
  - "Minimum 3 analysts ran"
  - "Gold filter produced summary with impact classification"
  - "All enriched files pass squad-agnosticism scan"
  - "Extraction report generated with all sections"
  - "No existing data deleted from reference files"
passing_threshold: "All checks pass"
```

---

## Anti-Patterns (Consolidated)

| Anti-Pattern | Why It's Wrong | Correct Approach |
|--------------|----------------|------------------|
| Extract without checking existing refs | Produces duplicates | ALWAYS run Phase 0 first |
| Single analyst extraction | Misses cross-framework insights | Minimum 3 analysts per squad |
| Skip gold filter (Phase 2) | Floods reference files with noise | Phase 2 is mandatory |
| Write business-specific data to squad | Violates squad agnosticism | Generalize or route to workspace/ |
| Overwrite existing reference sections | Loses previously extracted knowledge | Append-only merge strategy |
| Skip confidence markers | Agents cannot assess reliability | Every insight needs [DOC]/[REP]/[INF] |

---

## Related Tasks

| Task | Relationship |
|------|-------------|
| `deep-research-pre-agent.md` | Complementary (research before agent creation) |
| `etl-ops/tasks/process.md` | Upstream (produces the transcription) |
| `gerador-pop/tasks/extract-sop.md` | Downstream (uses enriched refs for SOPs) |
| `squad-creator/tasks/create-agent.md` | Downstream (agents consume reference data) |


_v2.0.0 -- decomposed from v1.0.0 monolith (461 lines) on 2026-03-26_

## Task Anatomy

- **Executor:** Agent
- **Inputs:** source_file; expert_slug; expert_name; target_squads
- **Outputs:** Updated squad reference files with new insights; Full summary with stats, conflicts, gaps
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Updated squad reference files with new insights
- [ ] Task output validated against quality standards
