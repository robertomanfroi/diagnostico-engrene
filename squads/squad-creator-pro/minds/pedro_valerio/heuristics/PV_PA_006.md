---
id: "PV_PA_006"
title: "Cryptographic Methodology (Clone vs Generic Agent)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Clone Strategy"
  - "SINKRA Governance"
pipeline_instances:
  - "brand-voice"
  - "methodology-enforcement"
sys_tension:
  - tension_with: "PV_PA_005 (Directed Stochasticity)"
    resolution: "PV_PA_006 enforces determinism via Clone architecture (95% rigidity); PV_PA_005 mandates variance as a feature. Resolution: Apply PV_PA_006 first (Phase 3 executor selection), then leverage PV_PA_005 within Clone boundaries (controlled randomness at Phase 4+ for flavor injection, not axiom compromise)."
  - tension_with: "PV_PA_001 (Systemic Coherence Scan)"
    resolution: "Both govern Phase 3 decisions but via different lenses: PV_PA_001 scans for systemic coherence; PV_PA_006 determines executor formality. Combined: PV_PA_001 identifies tension points, PV_PA_006 selects whether Generic Agent or Clone can resolve them."
---

# PV_PA_006 - Cryptographic Methodology (Clone vs Generic Agent)

**Type:** Decision Heuristic
**Phase:** 3 (Executor Selection)
**Agent:** @hybridOps:executor-designer
**Pattern:** HO-PP-003 (Quality Gate Pattern)

## Purpose

Enforce the boundary between a Generic Agent (which caps at ~70% methodology adherence) and a structural Clone (which delivers ~95% fidelity). Asserts that true brand voices, moral axioms, and specialist-level QA cannot be achieved via temporary prompting, requiring a rigid architecture.

## Configuration

```yaml
PV_PA_006:
  name: "Cryptographic Methodology"
  phase: 3
  pattern_reference: "HO-PP-003"

  weights:
    methodology_rigidity_req: 0.9
    brand_voice_fidelity: 0.8

  thresholds:
    clone_necessity_score: 0.85

  veto_conditions:
    - condition: "methodology_rigidity_req > 0.8 AND assigned_executor == 'Agent'"
      action: "VETO - Generic Agent insufficient; Requires formal Clone"

  output:
    type: "decision"
    values: ["ROUTE_TO_CLONE", "ROUTE_TO_AGENT", "VETO"]
```

## Application

**Input:** Brand Guideline enforcement, QA criteria mapping, Foundational tone replication.
**Process:** Determine if the task demands the strict extraction of a human expert's heuristics.
**Output:** ROUTE_TO_CLONE | ROUTE_TO_AGENT | VETO

## Decision Tree

```
PRIMARY BRANCH:
  IF (task involves strictly adhering to a proprietary methodology, tone of voice, or founders' heuristics)
    THEN ROUTE_TO_CLONE (Install Axiom architectures)

SECONDARY BRANCH:
  ELSE IF (task requires generic analysis, summarization, or standard semantic routing)
    THEN ROUTE_TO_AGENT

TERMINATION: "Act like X" prompts are for amateurs. True replication requires a repository of constraints.
CONSTRAINT: NEVER depend on a founder to review 100% of outputs if their heuristics can be cloned.
```

## Evaluation Criteria

| Criterion | Weight | Threshold | Description |
|-----------|--------|-----------|-------------|
| Axiom Rigidity | 0.9 | ≥0.8 | Does the entity possess strict "Rights and Wrongs"? |
| Voice Fidelity | 0.8 | ≥0.7 | Is the stylistic format (tone, pacing) non-negotiable? |
| Expert Bottleneck | 0.8 | ≥0.6 | Is an expert currently the operational bottleneck? |

## Confidence Requirements

- **High commitment decisions:** 95% threshold for converting critical expert operations into Clones; the core axioms must be perfectly mapped.
- **Tactical decisions:** Generic Agents are acceptable for internal operational summaries and agnostic tasks.

## Performance Metrics

```yaml
performance:
  decision_speed: "Immediate (routing phase)"
  accuracy_rate: "95% Adherence (vs 70% Generic)"
  confidence_level: "100% (eliminates 'AI-smell' from final output)"
  resource_efficiency: 9/10 (Expert time freed exponentially)
```

## Failure Modes

### Overloading the Prompt (The Coward)
- **Trigger:** Believing that writing a 3-page "System Prompt" on top of a standard ChatGPT window constitutes a Clone.
- **Manifestation:** Output degradations mid-chat, sudden losses of tone, constant human intervention required.
- **Detection:** AI generates generic "I hope this email finds you well" despite the prompt explicitly forbidding it.
- **Recovery:** Formalize the constraints into a structural engine (AIOX / Codex) that enforces Axioms at the system level.
- **Prevention:** Stop tweaking prompts; start building systems.

### Bloated Cloning (The Zealot)
- **Trigger:** Trying to build deep, heavy clones with 10k tokens of context for tasks like "Translating an FAQ".
- **Manifestation:** Excessive latency and API costs for zero real value gain.
- **Recovery:** Demote the executor to a Generic Agent or Worker. 

## Behavioral Evidence

**Example:** Replacing the Creative Director's QA
- **Context:** Allfluence team found AI copy to be "robotic" and relied entirely on the Director to rewrite it.
- **Information Available:** Prompt adjustments yielded diminishing returns.
- **Heuristic Application:** Deployed a strict Clone embedded with the Director's specific veto paths ("Cowardice", "Zealotry", "Over-explanation").
- **Outcome:** The Clone routinely rejected initial AI drafts automatically, citing the exact heuristics. The Director's review load dropped by 80%.

## Integration with HO-PP-003

This heuristic integrates with the Quality Gate Pattern at Phase 3:

```yaml
checkpoint:
  id: "clone-requirement-check"
  heuristic: PV_PA_006
  phase: 3

  criteria:
    - metric: "methodology_rigidity_req"
      threshold: 0.8
      operator: ">="
    - metric: "expert_bottleneck_score"
      threshold: 0.6
      operator: ">="

  veto_conditions:
    - condition: "fidelity_requirement == HIGH AND assigned_executor != 'Clone'"
      action: "HALT - Upgrade to Clone Architecture"

  validation_questions:
    - "Are there proprietary rules or extreme stylistic needs here?"
    - "Are we hitting the limit of 'prompt engineering'?"

  pass_action: "Assign Clone Executor"
  fail_action: "Fallback to Generic Agent"
```

---

## Validation

✓ **Paradox Identified:** The heuristic asserts that Generic Agents cannot exceed 70% fidelity while simultaneously requiring Clones for 95%+ adherence. Yet both operate within the same task domain. Resolution: Clones are not alternative paths—they are mandatory architectures for high-rigidity tasks. Generic Agents are valid only for low-rigidity, exploratory work.

✓ **System Tension Resolved:** PV_PA_006 creates apparent conflict with adaptive execution strategies (PV_PA_001, PV_PA_003) but resolves through hierarchical phase gates. Phase 3 decides executor type; Phases 4+ execute within that constraint.

✓ **Practical Validation:** Evidence from Allfluence case study confirms 80% reduction in Creative Director review load after Clone deployment, validating the ~25% fidelity gap assumption.

✓ **Constitutional Alignment:** Complies with SINKRA No-Invention principle by grounding Clone necessity in measurable axiom rigidity (≥0.8 threshold), not speculation.

**Pattern Compliance:** HO-PP-003 (Quality Gate) ✓
**Source:** SINKRA Book (Pedro Valério) - Part I
