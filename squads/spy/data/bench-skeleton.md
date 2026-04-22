# Benchmark Skeleton (Spy)

Canonical scaffold for universal benchmark output structure.
Use this as the reference when comparing any two subjects.

## 1) Universal Output Root

`docs/bench/{subject_a}-vs-{subject_b}/`

## 2) Universal Artifact Set

```
docs/bench/{subject_a}-vs-{subject_b}/
  ├── metadata.json                    # type, dimensions, date, profile
  ├── inventory-{subject_a}.json
  ├── inventory-{subject_a}.md
  ├── inventory-{subject_b}.json
  ├── inventory-{subject_b}.md
  ├── comparison-matrix.json
  ├── comparison-matrix.md
  ├── scorecard.json
  ├── scorecard.md
  ├── gap-analysis.json
  ├── gap-analysis.md
  ├── battle-card.md
  ├── executive-report.md
  └── deep/
      ├── {type-specific-1}.md
      └── {type-specific-2}.md
```

### Type-Specific Deep Artifacts

| Type | Deep Artifacts |
|------|---------------|
| codebase | `component-comparison.md`, `hooks-analysis.md`, `absorption-roadmap.md`, `migration-playbook.md` |
| llm | `reasoning-eval.md`, `coding-eval.md`, `cost-analysis.md`, `benchmark-compilation.md` |
| product | `feature-comparison.md`, `ux-analysis.md`, `pricing-analysis.md`, `reviews-sentiment.md` |
| company | `market-position.md`, `swot-analysis.md`, `financial-comparison.md`, `team-analysis.md` |
| technology | `maturity-assessment.md`, `ecosystem-analysis.md`, `dx-comparison.md`, `performance-benchmarks.md` |

## 3) Mandatory Mapping Logic

- Equivalence classes:
  - `Forte` (5/5)
  - `Parcial` (3/5)
  - `Sem equivalente` (1/5)
- Always map:
  - Subject A → Subject B
  - Subject B differentials (reverse mapping)
  - Subject A-only gaps
  - Subject B-only gaps

## 4) Scoring Dimensions

Dimensions are loaded dynamically from `data/bench-dimension-packs.yaml` based on comparison type.

| Type | Example Dimensions |
|------|-------------------|
| codebase | Architecture, Testing & QA, Documentation, Automation, Extensibility, Code Quality |
| llm | Reasoning, Coding, Math & Logic, Speed, Cost, Context Window, Tool Use |
| product | Features, UX/Design, Pricing, Integration, Support, Market Fit |
| company | Revenue, Market Share, Team, Funding, Technology, Brand |
| technology | Maturity, Ecosystem, DX, Performance, Scalability, Community |

Each dimension scored 0-100 for both subjects. Weights defined per dimension pack.

## 5) Required Core Sections (comparison-matrix.md)

1. Header: scope, date, comparison type, subjects
2. Sources (official docs/repos/data sources for both subjects)
3. Method (how data was collected and compared)
4. Inventory summary of both subjects
5. Feature/capability matrix with equivalence scores
6. Subject A-only capabilities
7. Subject B-only capabilities
8. Objective reading (strengths/weaknesses)
9. Recommendation or next-depth paths

## 6) Required Core Sections (scorecard.md)

1. Method type and dimension pack used
2. Dimension list with weights
3. Per-dimension score table (Subject A | Subject B | Delta)
4. Weighted totals
5. Confidence levels per dimension
6. Radar chart data reference
7. Objective reading
8. Generated files list

## 7) Minimum JSON Fields

### metadata.json
- `generatedAt`
- `comparison_type`
- `subjects.a` / `subjects.b`
- `dimension_pack`
- `scoring_dimensions[]`
- `profile`
- `pipeline_version`

### scorecard.json
- `generatedAt`
- `comparison_type`
- `subjects`
- `dimensions[]` with:
  - `name`
  - `weight`
  - `scores.subject_a`
  - `scores.subject_b`
  - `delta`
  - `confidence`
- `weighted_totals`
- `radar_chart_data`

### comparison-matrix.json
- `generatedAt`
- `comparison_type`
- `subjects`
- `categories[]` with:
  - `name`
  - `features[]` with:
    - `name`
    - `subject_a_value`
    - `subject_b_value`
    - `equivalence` (1-5)
    - `delta`
- `summary.total_features`
- `summary.a_only_count`
- `summary.b_only_count`

### gap-analysis.json
- `generatedAt`
- `subjects`
- `a_advantages[]`
- `b_advantages[]`
- Each gap: `name`, `severity`, `effort`, `strategic_value`, `description`

## 8) Quality Gate (Before Finish)

- All universal artifacts generated or explicitly marked as intentionally skipped
- All JSON parseable
- No invented claims (every assertion tied to source path/URL/data)
- Scoring method disclosed
- Confidence level disclosed for data quality
- Bidirectional gaps documented
- Sources cited for both subjects

---

## Legacy Codebase Format (Backward Compatible)

Existing benchmarks in `docs/bench/pai/`, `docs/bench/bmad/`, `docs/bench/openclaw/` use the legacy format below. These remain valid and are not affected by the universal upgrade.

### Legacy Output Root

`docs/bench/{competitor}/`

### Legacy Canonical Artifact Set (16 files)

1. `appendix-aiox-agent-command-inventory.json`
2. `appendix-aiox-workflow-sequence-inventory.json`
3. `appendix-exhaustive-agents-workflows-raw.json`
4. `{competitor}-vs-aiox-agents-command-matrix.md`
5. `{competitor}-vs-aiox-workflow-step-matrix.md`
6. `{competitor}-vs-aiox-comparativo-completo.md`
7. `benchmark-aiox-vs-{competitor}-scenarios.json`
8. `benchmark-aiox-vs-{competitor}-scenarios.md`
9. `{competitor}-features-para-aiox.md`
10. `roadmap-{competitor}-features-para-aiox.md`
11. `aiox-gap-closure-backlog-executable.json`
12. `aiox-gap-closure-backlog-executable.md`
13. `aiox-command-task-artifact-traceability-deep.md`
14. `appendix-command-task-artifact-traceability.json`
15. `{competitor}-to-aiox-migration-playbook-deep.md`
16. `comparacao-exaustiva-agentes-workflows-tasks.md`

### Legacy Scoring Axes

1. Delivery Control
2. QA Strength
3. Automation Index
4. Orchestration Depth
5. Drift Risk (lower is better)
