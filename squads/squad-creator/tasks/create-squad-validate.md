# Task: Squad Validation — Quality Loop (Validate, Fix, Optimize)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-squad-validate` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: create-squad-validate
name: "Squad Validation & Quality Loop"
category: squad-creation
agent: squad-chief
elicit: false
autonomous: true
description: "Run squad checklist, validate governance compliance, compute quality scoring, fix blocking issues through iterative cycles, optimize workflows for determinism, and present final summary."
accountability:
  human: squad-operator
  scope: full
domain: Operational
merged_from:
  - create-squad-validate v1.0.0
  - create-squad-fix v1.0.0
  - create-squad-optimize v1.0.0

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_squad_validate
Output: artifact::create_squad_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Validate the completed squad against the full checklist, governance compliance contract, and six quality dimensions. If issues are found, fix them through automated retry cycles. Optimize workflows for determinism and compliance. This is one iterative quality loop -- validate, fix, re-validate, optimize, re-validate -- not three separate tasks.

## Prerequisites

- [ ] `create-squad-build` completed (all components created and integrated)
- [ ] `checklists/squad-checklist.md` available
- [ ] `data/quality-dimensions-framework.md` loaded
- [ ] All agents, workflows, tasks, and documentation created
- [ ] Squad workflows exist at `squads/{squad_name}/workflows/*.yaml`
- [ ] Workflow contract schema available for re-validation

## Inputs

```yaml
inputs:
  build_output:
    type: object
    required: true
    description: "Output from create-squad-build"
    fields: [agents_created, workflows_created, tasks_created, templates_created, dependencies_wired, activation_surface_contract]
  squad_name:
    type: string
    required: true
  entry_agent:
    type: string
    required: true
```

## Workflow / Steps

### Step 5.1: Run Squad Checklist

**Execute: checklists/squad-checklist.md**

```yaml
run_squad_checklist:
  categories:
    - structure: "Directory structure correct"
    - agents: "All agents meet standards"
    - workflows: "All workflows have checkpoints"
    - tasks: "All tasks follow anatomy"
    - documentation: "README complete"
    - integration: "Dependencies wired + COO handoff prepared when workspace write is requested"

  blocking_items:
    - orchestrator_exists
    - tier_0_exists
    - quality_gates_defined
    - readme_complete
    - coo_handoff_exists_when_workspace_write_requested
```

### Step 5.2: Quality Dimensions Scoring

**Apply: quality-dimensions-framework.md**

```yaml
quality_scoring:
  dimensions:
    - accuracy: "Are agents well-researched and domain-accurate?"
    - coherence: "Do components work together?"
    - strategic_alignment: "Does squad serve purpose?"
    - operational_excellence: "Is squad usable?"
    - innovation_capacity: "Can squad grow?"
    - risk_management: "Are guardrails in place?"

  weights:
    accuracy: 0.20
    coherence: 0.20
    strategic_alignment: 0.15
    operational_excellence: 0.20
    innovation_capacity: 0.10
    risk_management: 0.15

  threshold: 7.0
  veto_if_below_5:
    - accuracy
    - coherence
    - operational_excellence
```

### Step 5.2b: Governance Compliance Validation

**Execute: validate-squad-classify (governance compliance check)**

```yaml
governance_compliance:
  required:
    - artifact_contracts[] present and non-empty
    - artifact_contract templates exist
    - bu_mapping defined
    - supported_modes[] valid
  on_fail:
    - BLOCK validation
    - report missing governance fields explicitly
```

### Step 5.3: Fix Blocking Issues (Iterative Cycle)

```yaml
fix_blocking_issues:
  trigger: "Any CRITICAL or HIGH failure from Steps 5.1, 5.2, or 5.2b"

  process:
    parse_failures:
      - Read validation results
      - Extract each failure with: category, severity (CRITICAL/HIGH/MEDIUM/LOW), file path, description
      - Sort by severity (CRITICAL first)
      - Skip LOW severity items (document only)

    apply_targeted_fixes:
      - For each CRITICAL/HIGH failure:
        - Read the affected file
        - Identify the specific issue (missing field, broken reference, schema violation)
        - Apply the minimal fix that resolves the issue
        - Log the fix: what changed, why, which file
      - For MEDIUM failures:
        - Attempt auto-fix if pattern is known
        - Otherwise document as technical debt

    revalidate:
      - Run the same validation checks from Steps 5.1/5.2/5.2b
      - Compare new results against previous iteration
      - If all CRITICAL/HIGH resolved: mark fix cycle as SUCCESS
      - If failures remain and iteration < max: return to apply_targeted_fixes
      - If failures remain and iteration == max: proceed to escalation

  max_iterations: 3
  on_max_iterations_exceeded:
    - Generate fix-cycle-log.md with iterations completed, fixes applied, remaining failures
    - report_remaining_issues
    - ask_human_for_direction

  fix_cycle_output:
    path: ".aiox/squad-runtime/create-squad/{squad_name}/validation/fix-cycle-log.md"
```

### Step 5.4: Optimize Workflows (Determinism Pass)

```yaml
optimize_workflows:
  scan:
    - Read all *.yaml files in squads/{squad_name}/workflows/
    - For each workflow, check:
      - Every phase has a task_ref pointing to an existing task file
      - All state transitions are reachable (no orphan states)
      - No ambiguous trigger names (unique per workflow)
      - on_success and on_failure handlers defined where needed

  apply_deterministic_fixes:
    - Missing task_ref: flag as CRITICAL (cannot auto-fix without task)
    - Orphan states: flag as HIGH, suggest removal
    - Duplicate triggers: rename with suffix to disambiguate
    - Missing handlers: add default on_failure handler where absent

  revalidate_contracts:
    - Run contract validation on all modified workflows
    - Confirm all workflows pass after optimization
    - If any fail, feed back into fix cycle (Step 5.3)

  output:
    analysis_summary:
      path: ".aiox/squad-runtime/create-squad/{squad_name}/validation/determinism-analysis.yaml"
    compliance_score: "0-10"
```

### Step 5.5: Pro Enhancement Suggestion

```yaml
pro_enhancement_check:
  check: "squads/squad-creator-pro/config.yaml exists?"

  if_pro_available:
    suggest: |
      Squad creation complete with base quality.
      For further improvement, squad-creator-pro is installed.
      Run *optimize to apply:
        - Mind-cloned agents based on real experts
        - Voice DNA extraction for authentic tone
        - Thinking DNA for expert-level reasoning
        - Advanced fidelity scoring and calibration

  if_pro_not_available:
    note: "Base squad created. For mind-cloned agents based on real experts, install squad-creator-pro."
```

### Step 5.6: Present Final Summary

```yaml
present_summary:
  created:
    - agents: "{N}"
    - workflows: "{N}"
    - tasks: "{N}"
    - templates: "{N}"
    - checklists: "{N}"

  quality:
    - overall_score: "{score}/10"
    - template_approach: "{approach}"
    - tier_coverage: "Full (0-3 + tools)"
    - governance_compliance: "PASS"
    - workflow_determinism: "{score}/10"

  activation:
    - install: "npm run install:squad {squad_name}"
    - activate: "@{squad_name}"
    - example: "@{squad_name}:{agent_name}"

  next_steps:
    optional_improvements:
      - "Add more specialists to Tier 3"
      - "Create domain-specific templates"
      - "Add integration tests"
      - "If squad-creator-pro installed, run *optimize for mind-cloned agents"

    handoff_to:
      - agent: "qa-architect"
        when: "Need deep validation audit"
      - agent: "domain-orchestrator"
        when: "Ready to use squad"
```

## Output

```yaml
validate_output:
  checklist_pass: true
  quality_score: "{score}/10"
  blocking_issues_resolved: "{N}"
  warnings: "{N}"
  governance_compliance: "PASS | FAIL"
  workflow_determinism_score: "{score}/10"
  fix_cycles_completed: "{N}"
  pro_available: "true | false"
  status: "PASS | FAIL"
  activation_command: "@{squad_name}"
```

## Acceptance Criteria

- [ ] Squad checklist passes (all blocking items green)
- [ ] `validate-squad-classify` passes with artifact contracts valid
- [ ] Quality score >= 7.0
- [ ] No dimension scores below 5 for accuracy, coherence, or operational_excellence
- [ ] Blocking issues resolved (or escalated after 3 iterations)
- [ ] All CRITICAL failures addressed within max iterations
- [ ] Each fix is minimal and targeted (no broad rewrites)
- [ ] Fix cycle log documents every change with rationale
- [ ] All workflows scanned for determinism issues
- [ ] Auto-fixable workflow issues applied without breaking contracts
- [ ] Determinism report generated with compliance score
- [ ] Re-validation confirms all workflows pass contracts
- [ ] CRITICAL issues (missing task_refs) are flagged, not silently skipped
- [ ] Final summary presented with activation instructions
- [ ] Runtime state updated to "validated"

## Veto Conditions

- **VETO-SQD-002:** Quality score < 7.0 after fix cycle exhausts max retries (3)
- **VETO-SQD-006:** All 3 smoke test scenarios fail (activation, help, basic_task)
- Any dimension (accuracy, coherence, operational_excellence) below 5.0
- Fix introduces new CRITICAL failures (regression)
- Fixes modify files outside the squad directory without justification
- Fix cycle exceeds max_iterations without escalation
- Optimization introduces breaking changes to workflow contracts
- Auto-fix removes phases or transitions without explicit approval

## Related Documents

- `create-squad.md` (parent composed task)
- `create-squad-build.md` (previous step)
- `create-squad-publish.md` (next step)
- `checklists/squad-checklist.md`
- `data/quality-dimensions-framework.md`
- `validate-squad-classify.md`

---

_Task Version: 2.0.0 (merged from: create-squad-validate v1.0.0 + create-squad-fix v1.0.0 + create-squad-optimize v1.0.0)_
_Last Updated: 2026-03-27_
