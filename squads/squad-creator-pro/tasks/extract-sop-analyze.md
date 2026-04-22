---
task-id: extract-sop-analyze
name: "Automation Analysis & Quality Assessment"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
estimated-time: 20 min
complexity: medium

inputs:
  required:
    - task_anatomy_map: "Mapped steps from Phase 2"
    - decision_rules: "Extracted rules from Phase 2"

outputs:
  primary:
    - automation_analysis: "Per-step automation recommendation"
    - quality_score: "META-AXIOMAS score (must be >= 7.0)"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-sop-analyze
  task_name: Automation Analysis & Quality Assessment
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 20m
  domain: Operational
  input:
  - '{''task_anatomy_map'': ''Mapped steps from Phase 2''}'
  - '{''decision_rules'': ''Extracted rules from Phase 2''}'
  output:
  - '{''automation_analysis'': ''Per-step automation recommendation''}'
  - '{''quality_score'': ''META-AXIOMAS score (must be >= 7.0)''}'
  action_items:
  - Automation Analysis (PV_PM_001)
  - Quality Assessment (META-AXIOMAS)
  acceptance_criteria:
  - Each step evaluated on 4 automation criteria
  - Decision matrix applied per step
  - META-AXIOMAS scored on all 10 dimensions
  - Overall score >= 7.0 (or VETO triggered)
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: Automation Analysis & Quality Assessment

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-sop-analyze` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-sop` (orchestrator stub)
- **Sequence:** Phase 3 of 4
- **Previous Task:** `extract-sop-extract`
- **Next Task:** `extract-sop-assemble`

## Purpose

Evaluate each step for automation potential using PV_PM_001 decision matrix, and score the overall process quality using META-AXIOMAS.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-ESP-003 | META-AXIOMAS score must be >= 7.0 | BLOCK - Review weak dimensions |

## Workflow / Steps

### Step 1: Automation Analysis (PV_PM_001)

For each step, evaluate:

| Criterion | Question |
|-----------|----------|
| Frequency | How often? (>4x/mo = high) |
| Impact | What if it fails? (business impact) |
| Automatability | Can code/AI do it? (determinism level) |
| Guardrails | Can we add safeguards? (required for automation) |

**Apply Decision Matrix:**
- AUTOMATE: High freq + High impact + High auto + Has guardrails
- DELEGATE: High freq + High impact + Low auto
- KEEP_MANUAL: Low freq + High impact
- ELIMINATE: Low freq + Low impact
- VETO: No guardrails possible

### Step 2: Quality Assessment (META-AXIOMAS)

Score the process on 10 dimensions (0-10):

1. Truthfulness -- Is the process described accurately?
2. Coherence -- Do steps align logically?
3. Strategic Alignment -- Does it serve business goals?
4. Operational Excellence -- Is it efficient?
5. Innovation Capacity -- Can it evolve?
6. Risk Management -- Are risks addressed?
7. Resource Optimization -- Is it lean?
8. Stakeholder Value -- Does it serve users?
9. Sustainability -- Is it maintainable?
10. Adaptability -- Can it handle change?

**Threshold:** Overall average >= 7.0 to proceed.

## Output

```yaml
automation_analysis:
  per_step:
    - step: ""
      frequency: "high|medium|low"
      impact: "high|medium|low"
      automatability: "high|medium|low"
      guardrails: true|false
      decision: "AUTOMATE|DELEGATE|KEEP_MANUAL|ELIMINATE|VETO"
  summary:
    automate: 0
    delegate: 0
    keep_manual: 0
    eliminate: 0
    veto: 0

quality_score:
  dimensions:
    truthfulness: 0
    coherence: 0
    strategic_alignment: 0
    operational_excellence: 0
    innovation_capacity: 0
    risk_management: 0
    resource_optimization: 0
    stakeholder_value: 0
    sustainability: 0
    adaptability: 0
  overall: 0.0
  passes_threshold: true|false
```

## Acceptance Criteria

- [ ] Each step evaluated on 4 automation criteria
- [ ] Decision matrix applied per step
- [ ] META-AXIOMAS scored on all 10 dimensions
- [ ] Overall score >= 7.0 (or VETO triggered)

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-sop.md` | Parent orchestrator |
| `extract-sop-extract.md` | Previous phase |
| `extract-sop-assemble.md` | Next phase |
