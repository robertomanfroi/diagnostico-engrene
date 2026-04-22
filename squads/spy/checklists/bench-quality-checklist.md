# Benchmark Quality Checklist

Pre-publication validation for all benchmark artifacts.
Run this checklist BEFORE considering any benchmark complete.

## Usage

Execute after completing a benchmark pipeline (`*bench {competitor}`).
Each section maps to artifact categories from the bench-skeleton.

---

## 1. Structural Integrity

- [ ] Output directory exists: `docs/bench/{competitor}/`
- [ ] All generated JSON files are valid (parseable without errors)
- [ ] All markdown files have proper heading hierarchy (H1 → H2 → H3)
- [ ] No empty sections or placeholder text left in outputs
- [ ] File naming follows canonical pattern from `bench-skeleton.md`

## 2. Source Citation

- [ ] Every competitor data point traces to a specific source (file path, URL, or API)
- [ ] Sources section lists ALL references used
- [ ] Method section describes HOW data was extracted (installed/baseline/docs)
- [ ] No data was invented or assumed without disclosure
- [ ] Confidence level stated for competitor data quality

## 3. AIOX Baseline Accuracy

- [ ] Agent count matches `Glob(".aiox-core/development/agents/*.md")` result
- [ ] Command count spot-checked against 2 random agents
- [ ] Workflow count matches `Glob(".aiox-core/development/workflows/*.yaml")` result
- [ ] Task count matches `Glob(".aiox-core/development/tasks/*.md")` result
- [ ] Squad count matches `Glob("squads/*/config.yaml")` result

## 4. Competitor Data Accuracy

- [ ] Agent names match source material exactly
- [ ] Command lists are from actual agent files (not inferred)
- [ ] Workflow names are real (not summarized or renamed)
- [ ] Counts are verified against source (not estimated)
- [ ] Version/date of competitor source documented

## 5. Scoring Objectivity

- [ ] All 5 axes scored for each scenario (Delivery Control, QA Strength, Automation Index, Orchestration Depth, Drift Risk)
- [ ] Scoring signals documented (what was counted/measured)
- [ ] Delta calculated correctly (AIOX - Competitor)
- [ ] No score inflation for AIOX or deflation for competitor
- [ ] Method disclosed: "installed" (real execution) vs "baseline" (docs-only)
- [ ] Structural metrics included (steps, agents, outputs, decision_points)

## 6. Mapping Quality

- [ ] Equivalence uses 3-level scale consistently (Forte / Parcial / Sem equivalente)
- [ ] OR uses 5-point paridade scale (5/5 to 1/5) with criteria
- [ ] Every mapping has specific delta description (not generic)
- [ ] AIOX differentials listed (features competitor lacks)
- [ ] Competitor gaps listed (features AIOX lacks)
- [ ] No agent/workflow left unmapped without explanation

## 7. Gap Analysis Completeness

- [ ] Every competitor-only feature identified
- [ ] Each feature has: description, value, complexity, priority
- [ ] Code references are real file paths (verified)
- [ ] Roadmap phases are ordered by priority × value
- [ ] Backlog items have acceptance criteria
- [ ] No feature duplicated across documents

## 8. Traceability (if included)

- [ ] Every AIOX agent covered
- [ ] Every command attempted for mapping
- [ ] Confidence scores assigned (high/medium/low/gap)
- [ ] Gaps flagged for manual validation
- [ ] Coverage percentage calculated and reported

## 9. Migration Playbook (if included)

- [ ] Every competitor agent has migration path
- [ ] Every core command has AIOX translation
- [ ] Migration waves are actionable (not generic)
- [ ] Risk checklists are specific (not boilerplate)
- [ ] Gap backlog has concrete closure items

## 10. Cross-Document Consistency

- [ ] Inventory counts consistent across all documents
- [ ] Agent names spelled consistently
- [ ] Paridade scores consistent between matrix and comparativo
- [ ] Gap lists consistent between comparativo and absorption
- [ ] Dates consistent across all outputs

---

## Scoring

| Checks Passed | Verdict |
|--------------|---------|
| >= 90% | APPROVED - Ready for reference |
| 70-89% | NEEDS REVISION - Fix flagged items |
| < 70% | REDO - Significant quality issues |

## Post-Checklist Actions

If APPROVED:
- [ ] Update `bench-skeleton.md` reference benchmarks table
- [ ] Notify team of new benchmark availability

If NEEDS REVISION:
- [ ] List specific items to fix
- [ ] Re-run affected task(s)
- [ ] Re-validate

If REDO:
- [ ] Identify root cause (bad source? wrong method?)
- [ ] Re-run full pipeline with corrected inputs
