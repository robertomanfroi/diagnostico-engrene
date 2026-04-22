# Task: Universal Weighted Scoring

## Contrato SINKRA

Domain: `Tactical`

responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- sujeitos, fontes e artefatos upstream conforme `Inputs`
Saida:
- artefatos de benchmark em `docs/bench/`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-score` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Agent` |
| **Estimated Duration** | `5-10min` |

## Metadata
```yaml
id: bench-score
name: "Universal Weighted Scoring"
category: benchmark-core
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "5-10min"
description: "Score two subjects on weighted dimensions from bench-dimension-packs.yaml, producing Forrester-style scorecards"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Score two subjects on the dimension pack matching their comparison type.
Each dimension is scored 0-100 based on observable signals from the inventories,
then weighted to produce a composite score. The output is a quantitative
scorecard in both JSON and Markdown formats.

This task replaces the fixed 5-axis scoring (Delivery Control, QA Strength, etc.)
from the legacy codebase-only benchmark system with a configurable, type-aware
scoring framework.

## Autonomous Execution Protocol

This task runs WITHOUT user interaction. Scores are derived from inventory
data and matrix comparisons. Every score must cite the signals that justify it.

---

## Prerequisites

- [ ] Both subject inventories available (`inventory-{slug}.json`)
- [ ] Comparison matrix available (`comparison-matrix.json`) — optional but improves accuracy
- [ ] Dimension pack loaded for the comparison type
- [ ] Data source config available (to determine scoring method label)

## Inputs

```yaml
inputs:
  inventory_a:
    type: object
    required: true
    description: "Parsed inventory JSON for Subject A"

  inventory_b:
    type: object
    required: true
    description: "Parsed inventory JSON for Subject B"

  comparison_type:
    type: enum
    required: true
    values: [codebase, llm, product, company, technology]

  dimensions:
    type: array
    required: true
    description: "Dimension pack from bench-dimension-packs.yaml"

  comparison_matrix:
    type: object
    required: false
    description: "Comparison matrix output (if available)"

  output_dir:
    type: string
    required: true
    description: "Output directory for scorecard files"
```

---

## Step 1: Validate Inputs

```
ACTION: Verify both inventories are non-empty
ACTION: Verify dimensions array has at least 3 entries
ACTION: Verify dimension weights sum to 1.0 (within 0.01 tolerance)

FAIL_CONDITION: Weights do not sum to ~1.0 → HALT with error listing actual sum
```

---

## Step 2: Determine Scoring Method

For each subject, determine how the data was collected:

```
ACTION: Check inventory method field

IF inventory.method == "autonomous-filesystem-scan":
  STORE: scoring_method = "installed"
  LABEL: "Installed benchmark — scored from local filesystem analysis"

ELSE IF inventory.method == "web-research":
  STORE: scoring_method = "baseline"
  LABEL: "Baseline benchmark — scored from public web data"

ELSE IF inventory.method == "web-research + github-stats":
  STORE: scoring_method = "baseline"
  LABEL: "Baseline benchmark — scored from public data + GitHub stats"

ELSE:
  STORE: scoring_method = "estimated"
  LABEL: "Estimated benchmark — limited data available"
```

STORE per subject: `method_a`, `method_b`, `label_a`, `label_b`

---

## Step 3: Score Each Dimension

For EACH dimension in `dimensions[]`:

```
ACTION: Evaluate dimension for Subject A
  - Identify relevant signals from dimension.signals[]
  - Find matching data points in inventory_a
  - Score 0-100 based on signal strength

ACTION: Evaluate dimension for Subject B
  - Same process against inventory_b

STORE in dimension_scores[]:
  {
    "dimension_id": "<id>",
    "dimension_name": "<name>",
    "weight": <weight>,
    "subject_a": {
      "score": <0-100>,
      "method": "<installed|baseline|estimated>",
      "signals_observed": [
        { "signal": "<name>", "value": "<observed value>", "contribution": "<how it affected score>" }
      ],
      "confidence": "<high|medium|low>",
      "justification": "<1-2 sentence explanation>"
    },
    "subject_b": {
      "score": <0-100>,
      "method": "<installed|baseline|estimated>",
      "signals_observed": [...],
      "confidence": "<high|medium|low>",
      "justification": "<1-2 sentence explanation>"
    },
    "delta": <subject_a.score - subject_b.score>,
    "advantage": "<A|B|TIE>"
  }
```

### Scoring Guidelines per Type

#### Codebase Scoring Signals

| Dimension | Score 90-100 | Score 60-89 | Score 30-59 | Score 0-29 |
|-----------|-------------|-------------|-------------|------------|
| Architecture | Clear separation, modular, layered | Good structure, minor coupling | Some structure, significant coupling | Monolithic, no clear structure |
| Testing & QA | >80% coverage, CI gates, multiple test types | 50-80% coverage, some CI | <50% coverage, basic tests | No tests or minimal |
| Documentation | Comprehensive README, API docs, inline | Good README, some docs | Basic README only | No meaningful docs |
| Automation | Full CI/CD, hooks, linting, formatting | CI pipeline, some automation | Manual build with scripts | No automation |
| Extensibility | Plugin system, config-driven, clear API | Some configurability | Hardcoded but modifiable | Closed, not extensible |
| Code Quality | Strict linting, types, consistent patterns | Good linting, mostly typed | Inconsistent patterns | No linting, no types |

#### LLM Scoring Signals

| Dimension | Score 90-100 | Score 60-89 | Score 30-59 | Score 0-29 |
|-----------|-------------|-------------|-------------|------------|
| Reasoning | MMLU >90, strong CoT | MMLU 80-90 | MMLU 60-80 | MMLU <60 |
| Coding | HumanEval >90, SWE-bench >40% | HumanEval 70-90 | HumanEval 50-70 | HumanEval <50 |
| Knowledge | Wide domain expertise, high factuality | Good knowledge, some gaps | Basic knowledge | Limited domain coverage |
| Safety | Low toxicity, good refusal, aligned | Mostly safe, some edge cases | Inconsistent safety | Known safety issues |
| Speed | <500ms TTFT, >100 tok/s | <1s TTFT, >50 tok/s | <3s TTFT, >20 tok/s | Slow responses |
| Cost | <$1/MTok input | $1-5/MTok | $5-15/MTok | >$15/MTok |
| Context | >200K tokens, high NIAH | 100-200K, good NIAH | 32-100K | <32K |

#### Product Scoring Signals

| Dimension | Score 90-100 | Score 60-89 | Score 30-59 | Score 0-29 |
|-----------|-------------|-------------|-------------|------------|
| Features | Industry-leading depth, unique capabilities | Comprehensive features | Basic feature set | Missing key features |
| UX | Exceptional onboarding, intuitive UI | Good UX, minor friction | Usable but clunky | Poor UX, steep learning curve |
| Pricing | Generous free tier, competitive paid | Fair pricing | Expensive for value | Overpriced or no free option |
| Integrations | 100+ integrations, open API, marketplace | 50+ integrations, API | 10-50, limited API | <10, no API |
| Support | 24/7 support, active community, docs | Good docs, community | Basic support | Minimal support |
| Scalability | Enterprise-ready, multi-tenant, high limits | Good scalability | Some limitations | Not scalable |

#### Company Scoring Signals

| Dimension | Score 90-100 | Score 60-89 | Score 30-59 | Score 0-29 |
|-----------|-------------|-------------|-------------|------------|
| Market Position | Market leader, >20% share | Strong challenger | Niche player | Unknown/new entrant |
| Innovation | Industry-defining products, patents | Regular innovation | Incremental improvements | Stagnant |
| Team | 500+ eng, strong culture, top talent | Growing team, good culture | Small team | Unknown team |
| Growth | >100% YoY | 50-100% YoY | 20-50% YoY | <20% or declining |
| Financial | Profitable or well-funded ($100M+) | Good funding ($10-100M) | Seed/early ($1-10M) | Unknown or risky |
| Ecosystem | Strong partner network, developer ecosystem | Some partnerships | Few partners | Isolated |

#### Technology Scoring Signals

| Dimension | Score 90-100 | Score 60-89 | Score 30-59 | Score 0-29 |
|-----------|-------------|-------------|-------------|------------|
| Maturity | 5+ years, stable API, semantic versioning | 2-5 years, mostly stable | 1-2 years, frequent breaking | <1 year, unstable |
| Ecosystem | 1000+ packages, rich tooling | 100-1000 packages | 10-100 packages | <10 packages |
| Performance | Industry-leading benchmarks | Above average | Average | Below average |
| DX | Excellent docs, IDE support, error messages | Good docs, decent tooling | Basic docs | Poor docs, no tooling |
| Community | 50K+ stars, 1K+ contributors, active | 10-50K stars, active | 1-10K stars | <1K stars, inactive |
| Adoption | Used by major companies, 1M+ downloads/wk | Growing adoption | Niche adoption | Minimal adoption |

---

## Step 4: Calculate Weighted Scores

```
ACTION: For each subject, compute weighted total:

weighted_score_a = SUM(dimension.score_a * dimension.weight) for all dimensions
weighted_score_b = SUM(dimension.score_b * dimension.weight) for all dimensions

STORE:
  total_a = round(weighted_score_a, 1)
  total_b = round(weighted_score_b, 1)
  total_delta = total_a - total_b
  overall_advantage = "A" if total_delta > 0 else "B" if total_delta < 0 else "TIE"
```

---

## Step 5: Determine Confidence Level

```
ACTION: Aggregate confidence across all dimensions:

IF all dimensions have confidence "high":
  STORE: overall_confidence = "high"
ELSE IF any dimension has confidence "low":
  STORE: overall_confidence = "low"
ELSE:
  STORE: overall_confidence = "medium"

STORE: confidence_note = explanation of what lowers/raises confidence
```

---

## Step 6: Generate Dimension Rankings

```
ACTION: Rank dimensions by delta (largest advantage first):

STORE: a_strongest[] = top 3 dimensions where A leads (by delta)
STORE: b_strongest[] = top 3 dimensions where B leads (by delta)
STORE: closest_dimensions[] = dimensions where |delta| < 5 (competitive areas)
```

---

## Step 7: Write Outputs

### 7.1: JSON Scorecard

```
STORE: scorecard = {
  "subject_a": { "name": subject_a_name, "method": method_a, "label": label_a },
  "subject_b": { "name": subject_b_name, "method": method_b, "label": label_b },
  "comparison_type": comparison_type,
  "generatedAt": "<ISO-8601>",
  "dimensions": dimension_scores[],
  "totals": {
    "subject_a": total_a,
    "subject_b": total_b,
    "delta": total_delta,
    "advantage": overall_advantage
  },
  "confidence": {
    "level": overall_confidence,
    "note": confidence_note
  },
  "rankings": {
    "a_strongest": a_strongest,
    "b_strongest": b_strongest,
    "closest": closest_dimensions
  }
}

ACTION: Write("{output_dir}/scorecard.json", JSON.stringify(scorecard, null, 2))
```

### 7.2: Markdown Scorecard

```
ACTION: Render scorecard as Markdown:

# {Subject A} vs {Subject B} — Scorecard

**Type:** {comparison_type}
**Generated:** {ISO-8601}
**Method:** {Subject A}: {label_a} | {Subject B}: {label_b}
**Overall Confidence:** {overall_confidence}

## Scores

| Dimension | Weight | {Subject A} | {Subject B} | Delta | Advantage |
|-----------|--------|------------|------------|-------|-----------|
| {name}    | {w}    | {score_a}  | {score_b}  | {d}   | {A/B/TIE} |
| ...       | ...    | ...        | ...        | ...   | ...       |
| **TOTAL** | **1.0**| **{total_a}** | **{total_b}** | **{total_delta}** | **{overall}** |

## {Subject A} Strengths
{a_strongest dimensions with justification}

## {Subject B} Strengths
{b_strongest dimensions with justification}

## Competitive Areas (Close Scores)
{closest_dimensions}

## Scoring Method
{Disclosure of how each score was derived}

## Signal Details
{For each dimension, list the signals observed and how they contributed}

ACTION: Write("{output_dir}/scorecard.md", rendered_markdown)
```

---

## Outputs

| File | Location | Format |
|------|----------|--------|
| Scorecard (JSON) | `{output_dir}/scorecard.json` | JSON |
| Scorecard (MD) | `{output_dir}/scorecard.md` | Markdown |

---

## Veto Conditions

The task MUST HALT if:

1. **Missing inventories** — Either inventory file does not exist or is empty.
2. **No dimensions** — Dimension pack is empty or not loaded for the comparison type.
3. **Weight sum invalid** — Dimension weights do not sum to approximately 1.0 (tolerance: 0.01).
4. **Type mismatch** — Inventories have different comparison types.
5. **Zero signals available** — For a given dimension, zero observable signals found in BOTH inventories. Skip dimension and note in output, but HALT if this affects >50% of dimensions.

---

## Scoring Integrity Rules

1. **No inflated scores** — Every score must cite specific signals that justify it. A score of 90+ requires strong, verifiable evidence.
2. **Method disclosure** — Every scorecard must state whether each subject was scored from local analysis ("installed") or web data ("baseline").
3. **Confidence per dimension** — Each dimension score has its own confidence level (high/medium/low).
4. **No invented signals** — If a signal cannot be observed, score as `null` and reduce confidence. Never fabricate data.
5. **Delta honesty** — Report negative deltas honestly. If Subject B leads, say so clearly.
6. **Weight transparency** — Always display the weight used for each dimension in the output.

---

## Verification

- [ ] JSON output is valid (parseable)
- [ ] All dimensions from the pack are scored (or explicitly marked as skipped with reason)
- [ ] Weighted totals are mathematically correct (recalculate to verify)
- [ ] Dimension weights in output match `bench-dimension-packs.yaml`
- [ ] Every score has at least one cited signal
- [ ] Scoring method disclosed for both subjects
- [ ] Confidence level assigned to each dimension and overall
- [ ] No score exceeds 100 or falls below 0
- [ ] Delta values are correct (A minus B)
- [ ] Markdown table renders correctly with consistent columns
- [ ] Rankings (strongest, closest) are derived from actual scores
