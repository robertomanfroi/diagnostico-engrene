# Synergy Analysis: {SUBJECT_A} + {SUBJECT_B}

**Type:** {COMPARISON_TYPE}
**Date:** {DATE}
**Prerequisite:** Benchmark `docs/bench/{SLUG}/` must exist with scorecard + gap-analysis
**Prepared by:** bench-analyst (autonomous)

---

## Executive Summary

{SYNERGY_EXECUTIVE_SUMMARY}

### Synergy Verdict

| Metric | Value |
|--------|-------|
| Synergy Class | {SYNERGY_CLASS: Complementary / Overlapping / Competing / Independent} |
| Synergy Score | {SYNERGY_SCORE}/100 |
| Integration Complexity | {LOW / MEDIUM / HIGH} |
| Combined Coverage | {COMBINED_COVERAGE}% of total capability space |
| Individual Coverage A | {COVERAGE_A}% |
| Individual Coverage B | {COVERAGE_B}% |
| Overlap (redundancy) | {OVERLAP_PCT}% |
| Net New (A+B > A or B) | {NET_NEW_PCT}% |
| Estimated Integration Effort | {EFFORT_ESTIMATE} |

---

## 1. Synergy Classification

### 1.1 Positioning Quadrant (Gartner-inspired)

```
    HIGH Autonomy
         │
    Q2   │   Q1
  Hermes │  HYBRID ← Ideal
  Domain │  Zone
─────────┼───────────── HIGH Coding Depth
    Q3   │   Q4
  Neither│  Claude Code
         │  Domain
    LOW Autonomy
```

**Position:** {QUADRANT_POSITION}
**Interpretation:** {QUADRANT_NARRATIVE}

### 1.2 Complementarity Index (Forrester-inspired)

| Dimension | {SUBJECT_A} Score | {SUBJECT_B} Score | Best-of | Overlap | Complementary? |
|-----------|:-----------------:|:-----------------:|:-------:|:-------:|:--------------:|
{FOR_EACH_DIMENSION}
| {DIM_NAME} | {SCORE_A} | {SCORE_B} | {BEST_SCORE} | {OVERLAP_TYPE: full/partial/none} | {YES/NO} |
{END_FOR}

**Complementarity Rate:** {COMPLEMENTARY_COUNT}/{TOTAL_DIMS} dimensions = {COMPLEMENTARITY_PCT}%
**Overlap Rate:** {OVERLAP_COUNT}/{TOTAL_DIMS} dimensions = {OVERLAP_PCT}%

---

## 2. Synergy Types (9-3-1 Framework)

### 2.1 Nine Synergy Categories

| # | Category | Type | Potential | Evidence | Effort |
|---|----------|:----:|:---------:|----------|:------:|
{FOR_EACH_SYNERGY}
| {N} | {CATEGORY_NAME} | {Revenue/Cost/Capability/Data/Workflow/Platform/Knowledge/Security/Brand} | {HIGH/MED/LOW/NONE} | {EVIDENCE} | {LOW/MED/HIGH} |
{END_FOR}

### 2.2 Three Priority Tiers

**TIER 1 — Immediate (0-30 days):**
{FOR_EACH_TIER1}
- **{SYNERGY_NAME}:** {DESCRIPTION}
  - Effort: {EFFORT} | ROI: {ROI} | Blocks: {DEPENDENCIES}
{END_FOR}

**TIER 2 — Short-term (30-90 days):**
{FOR_EACH_TIER2}
- **{SYNERGY_NAME}:** {DESCRIPTION}
  - Effort: {EFFORT} | ROI: {ROI} | Blocks: {DEPENDENCIES}
{END_FOR}

**TIER 3 — Strategic (90+ days):**
{FOR_EACH_TIER3}
- **{SYNERGY_NAME}:** {DESCRIPTION}
  - Effort: {EFFORT} | ROI: {ROI} | Blocks: {DEPENDENCIES}
{END_FOR}

### 2.3 One Integration Roadmap

```
{INTEGRATION_ROADMAP_ASCII}
```

---

## 3. Hybrid Architecture Design

### 3.1 Integration Topology

```
{ARCHITECTURE_DIAGRAM_ASCII}
```

### 3.2 Interface Contract

| Interface | From | To | Protocol | Data Flow | Latency |
|-----------|------|-----|----------|-----------|---------|
{FOR_EACH_INTERFACE}
| {INTERFACE_NAME} | {FROM_SUBJECT} | {TO_SUBJECT} | {PROTOCOL: MCP/API/CLI/Webhook/File} | {DATA_DESCRIPTION} | {LATENCY_REQUIREMENT} |
{END_FOR}

### 3.3 Responsibility Matrix (RACI)

| Capability | {SUBJECT_A} | {SUBJECT_B} | Hybrid |
|------------|:-----------:|:-----------:|:------:|
{FOR_EACH_CAPABILITY}
| {CAPABILITY} | {A_ROLE: R/A/C/I/-} | {B_ROLE: R/A/C/I/-} | {HYBRID_ROLE: description} |
{END_FOR}

### 3.4 Data Flow Diagram

```
{DATA_FLOW_DIAGRAM_ASCII}
```

---

## 4. Combined Capability Coverage

### 4.1 Capability Universe

All capabilities from both subjects, classified by coverage:

| # | Capability | {SUBJECT_A} | {SUBJECT_B} | Combined | Coverage Source |
|---|-----------|:-----------:|:-----------:|:--------:|:--------------:|
{FOR_EACH_CAPABILITY_UNIVERSE}
| {N} | {CAPABILITY} | {A_SCORE: 0-100} | {B_SCORE: 0-100} | {COMBINED: max(A,B)} | {A_ONLY / B_ONLY / BOTH / NEITHER} |
{END_FOR}

### 4.2 Coverage Analysis

```
{SUBJECT_A} alone:     ██████████████████░░░░░░░░  {COVERAGE_A}%
{SUBJECT_B} alone:     ████████████░░░░░░░░░░░░░░  {COVERAGE_B}%
Combined (best-of):    █████████████████████████░  {COMBINED_COVERAGE}%
Overlap (redundant):   ████░░░░░░░░░░░░░░░░░░░░░  {OVERLAP_PCT}%
Uncovered:             ░░░░░░░░░░░░░░░░░░░░░░░░░  {UNCOVERED_PCT}%
```

### 4.3 Exclusive Strengths

**Only {SUBJECT_A} provides:**
{FOR_EACH_A_EXCLUSIVE}
- {CAPABILITY} ({A_SCORE}/100) — {DESCRIPTION}
{END_FOR}

**Only {SUBJECT_B} provides:**
{FOR_EACH_B_EXCLUSIVE}
- {CAPABILITY} ({B_SCORE}/100) — {DESCRIPTION}
{END_FOR}

**Both provide (overlap):**
{FOR_EACH_OVERLAP}
- {CAPABILITY} — {A_SCORE} vs {B_SCORE}. Primary: {RECOMMENDED_PRIMARY}. Reason: {REASON}
{END_FOR}

---

## 5. Integration Patterns

### 5.1 Pattern Catalog

{FOR_EACH_PATTERN}
#### Pattern {N}: {PATTERN_NAME}

**Type:** {DELEGATION / ORCHESTRATION / PIPELINE / SIDECAR / GATEWAY / FALLBACK}
**Description:** {PATTERN_DESCRIPTION}

```
{PATTERN_DIAGRAM_ASCII}
```

**When to use:** {WHEN_TO_USE}
**Pros:** {PROS}
**Cons:** {CONS}
**Implementation:** {IMPLEMENTATION_NOTES}

---
{END_FOR}

### 5.2 Recommended Pattern

**Primary Pattern:** {RECOMMENDED_PATTERN_NAME}
**Rationale:** {RATIONALE}

---

## 6. Integration Friction Analysis

### 6.1 Friction Points

| # | Friction Point | Type | Severity | Mitigation |
|---|---------------|:----:|:--------:|------------|
{FOR_EACH_FRICTION}
| {N} | {FRICTION_DESCRIPTION} | {Technical/Operational/Commercial/Architectural} | {HIGH/MED/LOW} | {MITIGATION_STRATEGY} |
{END_FOR}

### 6.2 Compatibility Matrix

| Aspect | {SUBJECT_A} | {SUBJECT_B} | Compatible? | Notes |
|--------|-------------|-------------|:-----------:|-------|
| Language/Runtime | {A_LANG} | {B_LANG} | {YES/PARTIAL/NO} | {NOTES} |
| Communication | {A_COMM} | {B_COMM} | {YES/PARTIAL/NO} | {NOTES} |
| Auth/Security | {A_AUTH} | {B_AUTH} | {YES/PARTIAL/NO} | {NOTES} |
| Data Format | {A_DATA} | {B_DATA} | {YES/PARTIAL/NO} | {NOTES} |
| State Management | {A_STATE} | {B_STATE} | {YES/PARTIAL/NO} | {NOTES} |
| Deployment | {A_DEPLOY} | {B_DEPLOY} | {YES/PARTIAL/NO} | {NOTES} |

### 6.3 Risk Assessment

| Risk | Probability | Impact | Mitigation | Owner |
|------|:----------:|:------:|------------|-------|
{FOR_EACH_RISK}
| {RISK_DESCRIPTION} | {HIGH/MED/LOW} | {HIGH/MED/LOW} | {MITIGATION} | {OWNER} |
{END_FOR}

---

## 7. Value Proposition: Combined vs Standalone

### 7.1 Value Equation

```
V(A+B) = V(A) + V(B) + Synergy_Value - Integration_Cost - Friction_Cost

V({SUBJECT_A}) alone:    {VALUE_A}
V({SUBJECT_B}) alone:    {VALUE_B}
Synergy Value:           +{SYNERGY_VALUE}
Integration Cost:        -{INTEGRATION_COST}
Friction Cost:           -{FRICTION_COST}
─────────────────────────────────────
V(Combined):             {VALUE_COMBINED}
Net Synergy:             {NET_SYNERGY} ({NET_SYNERGY_PCT}% improvement over best standalone)
```

### 7.2 Use Case Matrix

| Use Case | {SUBJECT_A} Alone | {SUBJECT_B} Alone | Combined | Recommended |
|----------|:-----------------:|:-----------------:|:--------:|:-----------:|
{FOR_EACH_USE_CASE}
| {USE_CASE} | {A_RATING: 1-5} | {B_RATING: 1-5} | {COMBINED_RATING: 1-5} | {A / B / Combined} |
{END_FOR}

---

## 8. Implementation Roadmap

### Phase 0: Proof of Concept ({PHASE0_DURATION})
{PHASE0_DESCRIPTION}

**Deliverables:**
{FOR_EACH_PHASE0_DELIVERABLE}
- [ ] {DELIVERABLE}
{END_FOR}

**Success criteria:** {PHASE0_SUCCESS_CRITERIA}

### Phase 1: Core Integration ({PHASE1_DURATION})
{PHASE1_DESCRIPTION}

**Deliverables:**
{FOR_EACH_PHASE1_DELIVERABLE}
- [ ] {DELIVERABLE}
{END_FOR}

### Phase 2: Advanced Synergies ({PHASE2_DURATION})
{PHASE2_DESCRIPTION}

**Deliverables:**
{FOR_EACH_PHASE2_DELIVERABLE}
- [ ] {DELIVERABLE}
{END_FOR}

### Phase 3: Full Hybrid ({PHASE3_DURATION})
{PHASE3_DESCRIPTION}

**Deliverables:**
{FOR_EACH_PHASE3_DELIVERABLE}
- [ ] {DELIVERABLE}
{END_FOR}

---

## 9. Metrics & Success Criteria

### KPIs for Synergy Realization

| KPI | Baseline (standalone) | Target (combined) | Measurement |
|-----|:--------------------:|:-----------------:|-------------|
{FOR_EACH_KPI}
| {KPI_NAME} | {BASELINE} | {TARGET} | {MEASUREMENT_METHOD} |
{END_FOR}

### Decision Gate

**Proceed with integration if:**
{FOR_EACH_GATE_CRITERIA}
- [ ] {CRITERIA}
{END_FOR}

**Abort/Reconsider if:**
{FOR_EACH_ABORT_CRITERIA}
- [ ] {CRITERIA}
{END_FOR}

---

## Methodology

### Frameworks Applied

| Framework | Aspect | Adapted From |
|-----------|--------|-------------|
| Positioning Quadrant | Classification | Gartner Magic Quadrant (2-axis positioning) |
| Complementarity Index | Dimension analysis | Forrester Wave (weighted scoring, current vs strategy) |
| 9-3-1 Synergy | Category identification | BrightWolves 9-3-1 Framework (M&A synergy evaluation) |
| FIA | Battle card | Klue Fact-Impact-Act (competitive intelligence) |
| RACI | Responsibility | Standard responsibility assignment matrix |
| Value Equation | ROI | Stratechi synergy valuation (Revenue + Cost + Capital) |

### Data Sources

| Source | Type | Confidence |
|--------|------|:----------:|
{FOR_EACH_SOURCE}
| {SOURCE_NAME} | {SOURCE_TYPE} | {HIGH/MED/LOW} |
{END_FOR}

### Artifacts Consumed

| Artifact | Path | Status |
|----------|------|:------:|
| Benchmark Scorecard | docs/bench/{SLUG}/scorecard.json | {STATUS} |
| Gap Analysis | docs/bench/{SLUG}/gap-analysis.json | {STATUS} |
| Comparison Matrix | docs/bench/{SLUG}/comparison-matrix.json | {STATUS} |
| Battle Card | docs/bench/{SLUG}/battle-card.md | {STATUS} |
| Executive Report | docs/bench/{SLUG}/executive-report.md | {STATUS} |
{IF_INTERNAL_ANALYSES}
| Internal Analysis | {INTERNAL_PATH} | {STATUS} |
{END_IF}

---

## Appendix: Synergy Score Calculation

```
Synergy Score = (
  Complementarity Rate × 0.30 +
  Combined Coverage Uplift × 0.25 +
  Integration Feasibility × 0.20 +
  Value Equation Net Positive × 0.15 +
  Pattern Maturity × 0.10
) × 100

Where:
  Complementarity Rate = complementary_dims / total_dims
  Combined Coverage Uplift = (combined_coverage - max(a_coverage, b_coverage)) / (100 - max(a,b))
  Integration Feasibility = 1 - (friction_score / max_friction)
  Value Equation Net Positive = net_synergy / (value_a + value_b)
  Pattern Maturity = proven_patterns / total_patterns_needed
```

---

_Generated by bench-synergy task | Template: bench-synergy-tmpl.md v1.0.0_
_Frameworks: Gartner MQ + Forrester Wave + BrightWolves 9-3-1 + Klue FIA + Stratechi Synergy_
