---
id: "PV_PA_021"
title: "Clone Methodology Adherence"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Clone Architecture"
pipeline_instances:
  - "quality-control"
  - "brand-voice"
sys_tension:
  tension_with: "PV_PA_020 (Expert Verification Requirement)"
  resolution: "Clone ensures structural adherence (axioms + rules); Expert validates semantic intent + context fit. Clone is necessary but not sufficient."
---

# PV_PA_021 - Clone Methodology Adherence

**Type:** Decision Heuristic
**Phase:** 3 (Assignment)
**Agent:** @hybridOps:process-architect

## Purpose

A generic Agent mimics; a Clone embodies. When outputs require >95% adherence to a specific brand framework, founder's strict ruleset, or idiosyncratic corporate methodology, use a Clone architecture. A generic LLM with a 50-word prompt is insufficient.

## Configuration

```yaml
PV_PA_021:
  name: "Clone Methodology Adherence"
  phase: 3

  veto_conditions:
    - condition: "task_demands_company_voice_adherence > 90% AND executor == Agent_Generic"
      action: "VETO - Generic prompts degrade across large context windows. Build a Clone."
```

## Application

**Process:** Find areas where experts complain that the AI "just doesn't write like us" or "missed the specific company rule." Do not tweak the prompt; upgrade the executor to the Clone tier (Axioms injected directly into behavior).

## Decision Tree

```
IF (Output MUST sound structurally identical to Entity X or follow Framework Y without fault)
THEN EXECUTOR = CLONE.
```

## Failure Modes

### Generic Mimicry
- **Trigger:** Trying to use a base ChatGPT interface as a brand's critical Quality Assurance reviewer, only to find it approving generic corporate-speak that dilutes the brand.

---

## Validation

**Paradox Identified:** Clone architecture solves structural adherence through axioms and rules injection, but cannot guarantee semantic intent alignment or context-specific exceptions without human oversight.

**Resolution Path:**
- Clone handles >95% structural/methodological adherence (rules, tone, format)
- Expert (PV_PA_020) handles remaining 5%: semantic validation, exception cases, intent verification
- Combination is complementary: Clone automates rule enforcement; Expert validates judgment calls

**Applicability Check:**
- ✓ Brand voice consistency (>90% adherence required)
- ✓ Founder-specific methodologies (idiosyncratic rulesets)
- ✓ Corporate framework compliance (structured workflows)
- ✗ Novel judgment calls (always require Expert)
- ✗ Context exceptions (always require Expert)