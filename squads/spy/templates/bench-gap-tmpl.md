# Gap Analysis: {SUBJECT_A} vs {SUBJECT_B}

**Type:** {COMPARISON_TYPE}
**Date:** {DATE}
**Source Artifacts:** comparison-matrix.json, scorecard.json, inventory-a.json, inventory-b.json
**Slug:** {SLUG}

---

## Executive Summary

{GAP_EXECUTIVE_SUMMARY}

| Direction | Total Gaps | HIGH Impact | MED Impact | LOW Impact | P0 | P1 | P2 | P3 |
|-----------|:---------:|:----------:|:---------:|:---------:|:--:|:--:|:--:|:--:|
| Gaps of {SUBJECT_A} | {TOTAL_GAPS_A} | {HIGH_A} | {MED_A} | {LOW_A} | {P0_A} | {P1_A} | {P2_A} | {P3_A} |
| Gaps of {SUBJECT_B} | {TOTAL_GAPS_B} | {HIGH_B} | {MED_B} | {LOW_B} | {P0_B} | {P1_B} | {P2_B} | {P3_B} |

---

## Gaps of {SUBJECT_A}

What {SUBJECT_B} has that {SUBJECT_A} lacks or partially covers:

### Missing Capabilities (SEM_EQUIV)

| ID | Capability | Dimension | Impact | Complexity | Priority | Description |
|----|-----------|-----------|:------:|:----------:|:--------:|-------------|
{FOR_EACH_MISSING_GAP_A}
| {GAP_ID} | {CAPABILITY} | {DIMENSION} | {IMPACT} | {COMPLEXITY} | {PRIORITY} | {DESCRIPTION} |
{END_FOR}

### Partial Gaps (PARCIAL, {SUBJECT_B} Stronger)

| ID | Capability | What {SUBJECT_A} Has | What {SUBJECT_A} Lacks | Impact | Priority |
|----|-----------|---------------------|----------------------|:------:|:--------:|
{FOR_EACH_PARTIAL_GAP_A}
| {GAP_ID} | {CAPABILITY} | {WHAT_A_HAS} | {WHAT_A_LACKS} | {IMPACT} | {PRIORITY} |
{END_FOR}

### Gap Detail

{FOR_EACH_GAP_A}
#### {GAP_ID}: {CAPABILITY}

- **Type:** {MISSING/PARTIAL}
- **Dimension:** {DIMENSION}
- **Impact:** {IMPACT} — {IMPACT_JUSTIFICATION}
- **Complexity:** {COMPLEXITY} — {COMPLEXITY_JUSTIFICATION}
- **Priority:** {PRIORITY}
- **Evidence:** {EVIDENCE_REFERENCE}
{IF_PARTIAL}
- **What {SUBJECT_A} has:** {PARTIAL_COVERAGE}
- **What is missing:** {DELTA_DESCRIPTION}
{END_IF}

{END_FOR}

---

## Gaps of {SUBJECT_B}

What {SUBJECT_A} has that {SUBJECT_B} lacks or partially covers:

### Missing Capabilities (SEM_EQUIV)

| ID | Capability | Dimension | Impact | Complexity | Priority | Description |
|----|-----------|-----------|:------:|:----------:|:--------:|-------------|
{FOR_EACH_MISSING_GAP_B}
| {GAP_ID} | {CAPABILITY} | {DIMENSION} | {IMPACT} | {COMPLEXITY} | {PRIORITY} | {DESCRIPTION} |
{END_FOR}

### Partial Gaps (PARCIAL, {SUBJECT_A} Stronger)

| ID | Capability | What {SUBJECT_B} Has | What {SUBJECT_B} Lacks | Impact | Priority |
|----|-----------|---------------------|----------------------|:------:|:--------:|
{FOR_EACH_PARTIAL_GAP_B}
| {GAP_ID} | {CAPABILITY} | {WHAT_B_HAS} | {WHAT_B_LACKS} | {IMPACT} | {PRIORITY} |
{END_FOR}

### Gap Detail

{FOR_EACH_GAP_B}
#### {GAP_ID}: {CAPABILITY}

- **Type:** {MISSING/PARTIAL}
- **Dimension:** {DIMENSION}
- **Impact:** {IMPACT} — {IMPACT_JUSTIFICATION}
- **Complexity:** {COMPLEXITY} — {COMPLEXITY_JUSTIFICATION}
- **Priority:** {PRIORITY}
- **Evidence:** {EVIDENCE_REFERENCE}
{IF_PARTIAL}
- **What {SUBJECT_B} has:** {PARTIAL_COVERAGE}
- **What is missing:** {DELTA_DESCRIPTION}
{END_IF}

{END_FOR}

---

## Classification Matrix

### By Impact

| Impact | Gaps of {SUBJECT_A} | Gaps of {SUBJECT_B} |
|--------|:-------------------:|:-------------------:|
| HIGH | {HIGH_A} | {HIGH_B} |
| MED | {MED_A} | {MED_B} |
| LOW | {LOW_A} | {LOW_B} |

### By Complexity

| Complexity | Gaps of {SUBJECT_A} | Gaps of {SUBJECT_B} |
|------------|:-------------------:|:-------------------:|
| LOW | {LOW_COMPLEX_A} | {LOW_COMPLEX_B} |
| MED | {MED_COMPLEX_A} | {MED_COMPLEX_B} |
| HIGH | {HIGH_COMPLEX_A} | {HIGH_COMPLEX_B} |

### By Priority

| Priority | Gaps of {SUBJECT_A} | Gaps of {SUBJECT_B} |
|----------|:-------------------:|:-------------------:|
| P0 (critical) | {P0_A} | {P0_B} |
| P1 (high) | {P1_A} | {P1_B} |
| P2 (medium) | {P2_A} | {P2_B} |
| P3 (low) | {P3_A} | {P3_B} |

### Priority/Impact Heatmap

```
              LOW complexity    MED complexity    HIGH complexity
HIGH impact   P0 (quick win)   P1 (invest)       P2 (strategic)
MED impact    P1 (easy win)    P2 (moderate)      P3 (hard/moderate)
LOW impact    P3 (trivial)     P3 (low value)     P3 (avoid)
```

---

## Most Affected Dimensions

### For {SUBJECT_A}

| Dimension | Gap Count | Highest Priority | Cumulative Impact |
|-----------|:---------:|:----------------:|:-----------------:|
{FOR_EACH_AFFECTED_DIM_A}
| {DIMENSION} | {COUNT} | {HIGHEST_PRIORITY} | {CUMULATIVE_IMPACT} |
{END_FOR}

### For {SUBJECT_B}

| Dimension | Gap Count | Highest Priority | Cumulative Impact |
|-----------|:---------:|:----------------:|:-----------------:|
{FOR_EACH_AFFECTED_DIM_B}
| {DIMENSION} | {COUNT} | {HIGHEST_PRIORITY} | {CUMULATIVE_IMPACT} |
{END_FOR}

---

## Action Items

Priority P0 and P1 gaps that warrant immediate attention:

| # | Action | Target | Closes Gap | Dimension | Expected Impact | Priority |
|---|--------|--------|-----------|-----------|-----------------|:--------:|
{FOR_EACH_ACTION_ITEM}
| {N} | {ACTION_TITLE} | {TARGET_SUBJECT} | {GAP_ID} | {DIMENSION} | {EXPECTED_IMPACT} | {PRIORITY} |
{END_FOR}

### Action Detail

{FOR_EACH_ACTION_ITEM}
#### {N}. {ACTION_TITLE}

**Target:** {TARGET_SUBJECT}
**Closes gap:** {GAP_ID} ({CAPABILITY})
**Description:** {ACTION_DESCRIPTION}
**Expected score improvement:** {EXPECTED_IMPROVEMENT} in {DIMENSION}
**Dependencies:** {DEPENDENCIES_LIST}

{END_FOR}

---

## Methodology

- **Gap identification:** Based on comparison-matrix.json equivalence classifications
- **Impact assessment:** Derived from scorecard dimension weights and scores
- **Complexity assessment:** Type-specific criteria ({COMPARISON_TYPE} rules applied)
- **Priority matrix:** Impact x Complexity mapping (see heatmap above)
- **Confidence:** {CONFIDENCE_LEVEL}

---

_Generated by bench-gap task | Template: bench-gap-tmpl.md v1.0.0_
