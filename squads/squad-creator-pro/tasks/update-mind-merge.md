---
task-id: update-mind-merge
name: "Merge Strategy & Conflict Resolution"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
haiku_eligible: false
estimated-time: 15 min
complexity: medium

inputs:
  required:
    - existing_dna: "Parsed DNA from Phase 1"
    - voice_delta: "Voice DNA delta from Phase 2"
    - thinking_delta: "Thinking DNA delta from Phase 2"
  optional:
    - mode: "merge|replace|selective (default: merge)"

outputs:
  primary:
    - merge_plan: "Complete merge plan with resolved conflicts"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind-merge
  task_name: Merge Strategy & Conflict Resolution
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 15m
  domain: Strategic
  input:
  - '{''existing_dna'': ''Parsed DNA from Phase 1''}'
  - '{''voice_delta'': ''Voice DNA delta from Phase 2''}'
  - '{''thinking_delta'': ''Thinking DNA delta from Phase 2''}'
  - '{''mode'': ''merge|replace|selective (default: merge)''}'
  output:
  - '{''merge_plan'': ''Complete merge plan with resolved conflicts''}'
  action_items:
  - Select Merge Mode
  - Apply Merge Rules
  - Identify Conflicts
  - Resolve Conflicts
  acceptance_criteria:
  - Merge mode selected and applied
  - All conflicts identified and categorized
  - Auto-resolvable conflicts resolved per strategy
  - Human-required conflicts presented (if selective mode)
  - Protected sections verified as unchanged (unless human-approved)
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Merge Strategy & Conflict Resolution

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `update-mind-merge` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `update-mind` (orchestrator stub)
- **Sequence:** Phase 3 of 4
- **Previous Task:** `update-mind-extract`
- **Next Task:** `update-mind-apply`

## Purpose

Definir a estrategia de merge entre DNA existente e deltas extraidos, resolver conflitos, e produzir um plano de merge executavel.

## Prerequisites

- Phase 2 completed (voice_delta and thinking_delta available)

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-UPM-003 | Protected sections must not be replaced without human approval | BLOCK - Route through selective mode |

## Workflow / Steps

### Step 1: Select Merge Mode

| Mode | Behavior |
|------|----------|
| **merge** | Add new elements, preserve existing |
| **replace** | Replace sections where new is significantly better |
| **selective** | Checkpoint per section, user decides |

### Step 2: Apply Merge Rules

```yaml
merge_rules:
  additive:
    - power_words
    - signature_phrases
    - stories
    - heuristics
    - recognition_patterns
  protected:
    - primary_framework
    - identity_statement
    - veto_heuristics
  replace_if_better:
    - diagnostic_questions
    - objection_responses
    - decision_pipeline
```

### Step 3: Identify Conflicts

For each element in voice_delta and thinking_delta, compare against existing_dna:

```yaml
conflicts:
  - section: ""
    existing_value: ""
    new_value: ""
    recommendation: "keep|replace|merge"
    rationale: ""
```

### Step 4: Resolve Conflicts

```yaml
resolution_strategy:
  auto_resolve:
    - "New element does not exist in current -> ADD"
    - "Same element with more details -> ENRICH"
    - "Same element with additional examples -> ADD EXAMPLES"
  require_human:
    - "Direct contradiction in framework"
    - "Change in identity_statement"
    - "Removal of existing element"
```

If mode is `selective`, present each conflict to user for decision.

## Output

```yaml
merge_plan:
  mode: "merge|replace|selective"
  sections_to_update: []
  elements_to_add: []
  elements_to_enrich: []
  conflicts_auto_resolved: []
  conflicts_human_resolved: []
  protected_sections_unchanged: []
```

## Acceptance Criteria

- [ ] Merge mode selected and applied
- [ ] All conflicts identified and categorized
- [ ] Auto-resolvable conflicts resolved per strategy
- [ ] Human-required conflicts presented (if selective mode)
- [ ] Protected sections verified as unchanged (unless human-approved)
- [ ] Merge plan is complete and executable

## Related Documents

| Document | Relationship |
|----------|-------------|
| `update-mind.md` | Parent orchestrator |
| `update-mind-extract.md` | Previous phase |
| `update-mind-apply.md` | Next phase |
