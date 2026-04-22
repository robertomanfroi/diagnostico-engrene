# Quadrant Analysis: {QUADRANT_TITLE}

**Type:** {COMPARISON_TYPE}
**Date:** {DATE}
**Subjects:** {SUBJECT_COUNT} evaluated
**Inspired by:** Gartner Magic Quadrant methodology

---

## Axes Definition

| Axis | Label | Description | Range |
|------|-------|-------------|-------|
| **X-axis** | {X_AXIS_LABEL} | {X_AXIS_DESCRIPTION} | 0-100 |
| **Y-axis** | {Y_AXIS_LABEL} | {Y_AXIS_DESCRIPTION} | 0-100 |

### X-Axis: {X_AXIS_LABEL}

Measures: {X_AXIS_DETAILED_DESCRIPTION}

Scoring signals:
{FOR_EACH_X_SIGNAL}
- {SIGNAL_NAME}: {SIGNAL_DESCRIPTION} (weight: {SIGNAL_WEIGHT}%)
{END_FOR}

### Y-Axis: {Y_AXIS_LABEL}

Measures: {Y_AXIS_DETAILED_DESCRIPTION}

Scoring signals:
{FOR_EACH_Y_SIGNAL}
- {SIGNAL_NAME}: {SIGNAL_DESCRIPTION} (weight: {SIGNAL_WEIGHT}%)
{END_FOR}

---

## Quadrant Map

```
                        {Y_AXIS_LABEL}
                             100
                              |
       CHALLENGERS            |            LEADERS
       (High Y, Low X)       |            (High X, High Y)
                              |
{FOR_EACH_SUBJECT_CHALLENGERS}
       {ICON} {SUBJECT_NAME}  |
          ({X},{Y})           |
{END_FOR}                     |  {FOR_EACH_SUBJECT_LEADERS}
                              |  {ICON} {SUBJECT_NAME}
                              |     ({X},{Y})
                              |  {END_FOR}
   ───────────────────────────┼──────────────────────── {X_AXIS_LABEL}
                              |                         100
       NICHE PLAYERS          |            VISIONARIES
       (Low X, Low Y)        |            (High X, Low Y)
                              |
{FOR_EACH_SUBJECT_NICHE}      |  {FOR_EACH_SUBJECT_VISIONARIES}
       {ICON} {SUBJECT_NAME}  |  {ICON} {SUBJECT_NAME}
          ({X},{Y})           |     ({X},{Y})
{END_FOR}                     |  {END_FOR}
                              |
                              0
```

---

## Subject Positioning

| Subject | X ({X_AXIS_LABEL}) | Y ({Y_AXIS_LABEL}) | Quadrant |
|---------|:------------------:|:------------------:|----------|
{FOR_EACH_SUBJECT}
| {SUBJECT_NAME} | {X_SCORE}/100 | {Y_SCORE}/100 | {QUADRANT_NAME} |
{END_FOR}

---

## Quadrant Summary

### Leaders (High {X_AXIS_LABEL}, High {Y_AXIS_LABEL})

{IF_LEADERS_EXIST}
{FOR_EACH_LEADER}
#### {SUBJECT_NAME} — X: {X_SCORE}, Y: {Y_SCORE}

{LEADER_JUSTIFICATION}

**Key strengths:**
{FOR_EACH_STRENGTH}
- {STRENGTH_DESCRIPTION}
{END_FOR}

**Watch areas:**
{FOR_EACH_WATCH_AREA}
- {WATCH_DESCRIPTION}
{END_FOR}

{END_FOR}
{ELSE}
_No subjects positioned as Leaders in this analysis._
{END_IF}

---

### Challengers (High {Y_AXIS_LABEL}, Lower {X_AXIS_LABEL})

{IF_CHALLENGERS_EXIST}
{FOR_EACH_CHALLENGER}
#### {SUBJECT_NAME} — X: {X_SCORE}, Y: {Y_SCORE}

{CHALLENGER_JUSTIFICATION}

**Key strengths:**
{FOR_EACH_STRENGTH}
- {STRENGTH_DESCRIPTION}
{END_FOR}

**Path to Leaders quadrant:**
{FOR_EACH_IMPROVEMENT}
- {IMPROVEMENT_DESCRIPTION}
{END_FOR}

{END_FOR}
{ELSE}
_No subjects positioned as Challengers in this analysis._
{END_IF}

---

### Visionaries (High {X_AXIS_LABEL}, Lower {Y_AXIS_LABEL})

{IF_VISIONARIES_EXIST}
{FOR_EACH_VISIONARY}
#### {SUBJECT_NAME} — X: {X_SCORE}, Y: {Y_SCORE}

{VISIONARY_JUSTIFICATION}

**Key strengths:**
{FOR_EACH_STRENGTH}
- {STRENGTH_DESCRIPTION}
{END_FOR}

**Path to Leaders quadrant:**
{FOR_EACH_IMPROVEMENT}
- {IMPROVEMENT_DESCRIPTION}
{END_FOR}

{END_FOR}
{ELSE}
_No subjects positioned as Visionaries in this analysis._
{END_IF}

---

### Niche Players (Lower {X_AXIS_LABEL}, Lower {Y_AXIS_LABEL})

{IF_NICHE_EXIST}
{FOR_EACH_NICHE}
#### {SUBJECT_NAME} — X: {X_SCORE}, Y: {Y_SCORE}

{NICHE_JUSTIFICATION}

**Target use case:**
{NICHE_USE_CASE}

**Path to advancement:**
{FOR_EACH_IMPROVEMENT}
- {IMPROVEMENT_DESCRIPTION}
{END_FOR}

{END_FOR}
{ELSE}
_No subjects positioned as Niche Players in this analysis._
{END_IF}

---

## Axis Configuration Reference

### Recommended Axes by Comparison Type

| Type | X-Axis | Y-Axis |
|------|--------|--------|
| **company** | Completeness of Vision | Ability to Execute |
| **product** | Feature Completeness | Market Presence |
| **technology** | Innovation / Future Readiness | Ecosystem Maturity |
| **codebase** | Architecture Quality | Feature Coverage |
| **llm** | Capability Breadth | Performance / Reliability |

### Custom Axes

This template supports any custom axis configuration. To use custom axes,
provide `x_axis_label`, `x_axis_description`, `y_axis_label`, and
`y_axis_description` as input parameters.

---

## Methodology

### Positioning Method

Each subject is scored independently on both axes using the signals defined above.
Scores are normalized to the 0-100 range. Quadrant boundaries are at the 50-point
mark on each axis.

### Quadrant Definitions

| Quadrant | X Range | Y Range | Interpretation |
|----------|---------|---------|---------------|
| **Leaders** | 50-100 | 50-100 | Strong on both axes — established and innovative |
| **Challengers** | 0-49 | 50-100 | Strong execution but limited vision/breadth |
| **Visionaries** | 50-100 | 0-49 | Innovative but limited execution/presence |
| **Niche Players** | 0-49 | 0-49 | Focused scope, may excel in specific niches |

### Data Sources

{FOR_EACH_SUBJECT}
- **{SUBJECT_NAME}:** {DATA_SOURCE_DESCRIPTION}
{END_FOR}

### Confidence

{CONFIDENCE_DISCLOSURE}

---

_Generated by bench-score task (quadrant mode) | Template: bench-quadrant-tmpl.md v1.0.0_
