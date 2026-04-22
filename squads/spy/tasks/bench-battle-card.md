# Task: Universal Battle Card Generator (Autonomous)

## Contrato SINKRA

Domain: `Strategic`

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
| **Task ID** | `bench-battle-card` |
| **Version** | `1.0.0` |
| **Status** | `pending` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Agent` |
| **Model** | `claude-sonnet-4-20250514` |
| **Haiku Eligible** | `false` |
| **Estimated Duration** | `8-15min` |

## Metadata
```yaml
id: bench-battle-card
name: "Universal Battle Card Generator"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "8-15min"
description: "Generate a 1-page quick comparison battle card for decision makers — works for any comparison type (codebase, LLM, product, company, technology)"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Produce a single-page, side-by-side battle card that gives decision makers an instant
comparative overview of two subjects. Inspired by Forrester Wave quadrant summaries
and sales battle cards used in enterprise software.

The battle card distills all benchmark artifacts (inventories, scorecard, comparison
matrix, gap analysis) into a concise, scannable format with:
- Quick specs comparison table
- Score per dimension with winner indicators
- Strengths and weaknesses of each subject
- TL;DR verdict with actionable recommendation

This format works for ANY comparison type: codebases, LLMs, products, companies,
or technologies. The card adapts its "Quick Specs" section based on type.

## Input

| Input | Type | Required | Source |
|-------|------|----------|--------|
| `subject_a` | string | YES | Pipeline param |
| `subject_b` | string | YES | Pipeline param |
| `comparison_type` | string | YES | One of: codebase, llm, product, company, technology |
| `inventory_a` | file | YES | Output from `bench-inventory-type` (inventory-a.json) |
| `inventory_b` | file | YES | Output from `bench-inventory-type` (inventory-b.json) |
| `scorecard` | file | YES | Output from `bench-score` (scorecard.json) |
| `comparison_matrix` | file | NO | Output from `bench-compare` (comparison-matrix.json) |
| `gap_analysis` | file | NO | Output from `bench-gap` (gap-analysis.json) |
| `profile` | string | NO | Target audience profile (default: "Technical Decision Maker") |

## Output

| Output | Format | Destination |
|--------|--------|-------------|
| Battle card | Markdown | `docs/bench/{slug}/battle-card.md` |

Where `{slug}` = `{subject_a}-vs-{subject_b}` (kebab-case, lowercase).

## Prerequisites

- [ ] Both inventories exist from `bench-inventory-type`
- [ ] Scorecard exists from `bench-score`
- [ ] Comparison matrix recommended (enriches the card) but not blocking
- [ ] Gap analysis recommended (enriches strengths/weaknesses) but not blocking

---

## Veto Conditions

The task MUST NOT execute (or must HALT immediately) if:

1. **No scorecard available** -- The battle card requires scored dimensions. Run `bench-score` first.
2. **Missing inventories** -- Cannot build Quick Specs table without both inventories.
3. **comparison_type not recognized** -- Must be one of: codebase, llm, product, company, technology.
4. **Scorecard has zero dimensions** -- Corrupt or empty scorecard cannot produce a battle card.
5. **Output file already exists and is less than 24h old** -- Do not overwrite unless `--force` specified.

---

## Autonomous Execution Protocol

This task runs WITHOUT user interaction. Execute all steps sequentially,
synthesize data from upstream artifacts, and produce the battle card.

**CRITICAL RULES:**
- Battle card MUST fit conceptually on ONE page (concise, no filler)
- Every data point must trace to an upstream artifact (inventory, scorecard, matrix, gaps)
- Winner indicators must be objective (based on scores, not opinion)
- Strengths/Weaknesses must be specific (cite the dimension or capability, not vague)
- Verdict must be balanced and professional (acknowledge both subjects' merits)
- NO invented data -- if an input is missing, state "Data not available" not a guess

---

## Step 1: Load All Available Artifacts

```
ACTION: Read("docs/bench/{slug}/inventory-a.json")
STORE: inv_a

ACTION: Read("docs/bench/{slug}/inventory-b.json")
STORE: inv_b

ACTION: Read("docs/bench/{slug}/scorecard.json")
STORE: scorecard

OPTIONAL:
  ACTION: Read("docs/bench/{slug}/comparison-matrix.json")
  STORE: matrix (or null if not found)

  ACTION: Read("docs/bench/{slug}/gap-analysis.json")
  STORE: gaps (or null if not found)
```

---

## Step 2: Build Quick Specs Table (Type-Specific)

```
DEPENDING on comparison_type, SELECT relevant quick specs:

IF comparison_type == "codebase":
  specs = [
    { name: "Language/Stack", extract from inventories },
    { name: "Agents/Roles", count from inventories },
    { name: "Tasks/Commands", count from inventories },
    { name: "Workflows", count from inventories },
    { name: "Templates", count from inventories },
    { name: "Test Coverage", extract from inventories },
    { name: "License", extract from inventories },
    { name: "Last Updated", extract from inventories }
  ]

IF comparison_type == "llm":
  specs = [
    { name: "Provider", extract from inventories },
    { name: "Model Size", extract from inventories },
    { name: "Context Window", extract from inventories },
    { name: "Multimodal", extract from inventories },
    { name: "Function Calling", extract from inventories },
    { name: "Streaming", extract from inventories },
    { name: "Pricing (input/1K)", extract from inventories },
    { name: "Pricing (output/1K)", extract from inventories }
  ]

IF comparison_type == "product":
  specs = [
    { name: "Category", extract from inventories },
    { name: "Pricing Model", extract from inventories },
    { name: "Free Tier", extract from inventories },
    { name: "API Available", extract from inventories },
    { name: "Integrations", count from inventories },
    { name: "Platform", extract from inventories },
    { name: "Enterprise Ready", extract from inventories },
    { name: "Founded/Released", extract from inventories }
  ]

IF comparison_type == "company":
  specs = [
    { name: "Founded", extract from inventories },
    { name: "Employees", extract from inventories },
    { name: "Revenue (est.)", extract from inventories },
    { name: "Funding", extract from inventories },
    { name: "Market Segment", extract from inventories },
    { name: "Key Products", extract from inventories },
    { name: "Global Presence", extract from inventories },
    { name: "Public/Private", extract from inventories }
  ]

IF comparison_type == "technology":
  specs = [
    { name: "Type", extract from inventories },
    { name: "First Release", extract from inventories },
    { name: "Latest Version", extract from inventories },
    { name: "License", extract from inventories },
    { name: "Package Ecosystem", count from inventories },
    { name: "Community Size", extract from inventories },
    { name: "Corporate Backing", extract from inventories },
    { name: "Specification", extract from inventories }
  ]

STORE: quick_specs[]
```

---

## Step 3: Build Dimension Scores Table

```
ACTION: Extract from scorecard:
  FOR EACH dimension in scorecard.dimensions[]:
    EXTRACT:
      - dimension_name
      - score_a
      - score_b
      - weight
      - winner (A if score_a > score_b, B if score_b > score_a, TIE if equal)

  COMPUTE winner_indicator:
    IF score_a > score_b by >= 10 points: "◀◀ {subject_a}"
    IF score_a > score_b by < 10 points:  "◀ {subject_a}"
    IF score_b > score_a by >= 10 points: "{subject_b} ▶▶"
    IF score_b > score_a by < 10 points:  "{subject_b} ▶"
    IF |score_a - score_b| < 3:           "≈ TIE"

  EXTRACT weighted totals:
    - total_a = scorecard.weighted_total_a
    - total_b = scorecard.weighted_total_b
    - overall_winner

STORE: dimension_scores[], totals
```

---

## Step 4: Extract Strengths & Weaknesses

```
FOR subject_a:
  STRENGTHS: Dimensions where A scores > B by >= 5 points
    FORMAT: "{dimension}: {specific capability or advantage}"
    MAX: 4 strengths (pick highest deltas)

  WEAKNESSES: Dimensions where A scores < B by >= 5 points
    FORMAT: "{dimension}: {specific gap or disadvantage}"
    MAX: 4 weaknesses (pick highest negative deltas)

  IF gap_analysis available:
    ENRICH weaknesses with specific gap descriptions from gaps.gaps_of_a[]
    ENRICH strengths with specific unique capabilities from gaps.gaps_of_b[]

FOR subject_b:
  SAME logic, inverted perspective

STORE: a_strengths, a_weaknesses, b_strengths, b_weaknesses
```

---

## Step 5: Generate Verdict & Recommendation

```
ANALYZE:
  - overall_winner (from weighted scores)
  - dimension_wins_a = count of dimensions where A wins
  - dimension_wins_b = count of dimensions where B wins
  - margin = |total_a - total_b|

GENERATE verdict (2-3 sentences):
  IF margin >= 15: "{winner} has a clear advantage, particularly in {top_dimensions}."
  IF margin 5-14:  "{winner} edges ahead, with notable strengths in {top_dimensions}, though {loser} competes strongly in {counter_dimensions}."
  IF margin < 5:   "Both subjects are closely matched. {A} excels in {dims} while {B} leads in {other_dims}."

GENERATE recommendation (1-2 sentences):
  - Type-specific actionable advice
  IF codebase: "Choose {X} if you prioritize {dims}; choose {Y} for {other_dims}."
  IF llm: "Use {X} for {use_case}; consider {Y} for {other_use_case}."
  IF product: "Evaluate {X} if {criteria}; {Y} may be better for {other_criteria}."
  IF company: "{X} leads in {market_segment}; {Y} is stronger in {other_segment}."
  IF technology: "Adopt {X} for {scenario}; {Y} is preferable for {other_scenario}."

STORE: verdict_text, recommendation_text
```

---

## Step 6: Assemble Battle Card

```
ACTION: Write("docs/bench/{slug}/battle-card.md")

Use template: bench-battle-card-tmpl.md

POPULATE all template variables:
  {SUBJECT_A} = subject_a
  {SUBJECT_B} = subject_b
  {COMPARISON_TYPE} = comparison_type
  {DATE} = current date (YYYY-MM-DD)
  {PROFILE} = profile or "Technical Decision Maker"
  {FOR_EACH_SPEC} = quick_specs[]
  {FOR_EACH_DIMENSION} = dimension_scores[]
  {TOTAL_A} = weighted_total_a
  {TOTAL_B} = weighted_total_b
  {OVERALL_WINNER} = overall_winner
  {A_STRENGTHS} = a_strengths (comma-separated, concise)
  {A_WEAKNESSES} = a_weaknesses (comma-separated, concise)
  {B_STRENGTHS} = b_strengths (comma-separated, concise)
  {B_WEAKNESSES} = b_weaknesses (comma-separated, concise)
  {VERDICT_TEXT} = verdict_text
  {RECOMMENDATION} = recommendation_text
```

---

## Step 7: Validate Output

```
ACTION: Read the generated battle-card.md
VERIFY:
  - All template placeholders resolved (no remaining {PLACEHOLDER} text)
  - Quick Specs table has 6-8 rows
  - Dimension Scores table has all dimensions from scorecard
  - Strengths/Weaknesses are specific (not vague)
  - Verdict is balanced and professional
  - Recommendation is actionable
  - Document is concise (target: 60-100 lines, MAX 120 lines)

REPORT completion:
  - Specs compared: {count}
  - Dimensions scored: {count}
  - Overall winner: {subject}
  - Margin: {delta} points
  - Battle card length: {lines} lines
```

---

## Acceptance Criteria

The task is complete when ALL of the following are met:

- [ ] **AC-1:** `battle-card.md` exists at `docs/bench/{slug}/battle-card.md`
- [ ] **AC-2:** Quick Specs table has type-appropriate rows (6-8 specs)
- [ ] **AC-3:** Dimension Scores table includes ALL dimensions from the scorecard
- [ ] **AC-4:** Winner indicator shown for each dimension AND overall
- [ ] **AC-5:** Strengths and Weaknesses listed for BOTH subjects (max 4 each)
- [ ] **AC-6:** Strengths/Weaknesses are specific (cite dimension or capability, not vague)
- [ ] **AC-7:** TL;DR Verdict is present and balanced
- [ ] **AC-8:** Recommendation is actionable and type-appropriate
- [ ] **AC-9:** No template placeholders remaining (all {VARS} resolved)
- [ ] **AC-10:** Document is concise (under 120 lines)
- [ ] **AC-11:** All data traceable to upstream artifacts (no invented numbers)

## Quality Validation

After generation, validate:

- [ ] All markdown tables are syntactically valid
- [ ] Winner indicators are consistent with actual scores
- [ ] No broken references or placeholder text
- [ ] Strengths/Weaknesses don't contradict scorecard data
- [ ] Verdict aligns with the overall weighted scores

---

## Error Handling

| Error | Detection | Recovery |
|-------|-----------|----------|
| Scorecard not found | File read fails | HALT: "Run bench-score first" |
| Inventory not found | File read fails | HALT: "Run bench-inventory-type first" |
| Scorecard empty (0 dims) | Dimension list empty | HALT: "Scorecard has no dimensions" |
| Gap analysis not found | File read fails | WARN: proceed without gap enrichment |
| Comparison matrix not found | File read fails | WARN: proceed without matrix data |
| Inventory field missing | Key not in JSON | Use "N/A" for that spec row |
| comparison_type unrecognized | Type not in list | HALT: "Unrecognized comparison_type" |

## Integration

| Task | Relationship |
|------|-------------|
| `bench-inventory-type` | Upstream -- provides inventory data for Quick Specs |
| `bench-score` | Upstream -- provides dimension scores and weighted totals |
| `bench-compare` | Upstream (optional) -- enriches comparison context |
| `bench-gap` | Upstream (optional) -- enriches strengths/weaknesses |
| `bench-report` | Downstream -- executive report includes battle card summary |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-02-17_
_Compliant: Yes_
