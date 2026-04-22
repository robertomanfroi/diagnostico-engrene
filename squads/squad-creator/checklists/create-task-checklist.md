# Create Task Checklist

```yaml
checklist:
  id: create-task-checklist
  version: 1.0.0
  created: 2026-03-26
  purpose: "Validate task creation meets AIOX quality standards and Task Anatomy (HO-TP-001)"
  mode: blocking
  task_reference: tasks/create-task.md
  related_checklist: checklists/task-anatomy-checklist.md
```

---

## Pre-Creation Requirements

```yaml
pre_creation:
  - id: squad-exists
    check: "Target squad exists with valid config.yaml"
    type: blocking
    validation: "squads/{squad_name}/config.yaml exists and passes yamllint"

  - id: task-not-duplicate
    check: "No existing task with same purpose in target squad"
    type: blocking
    validation: "grep task_name across tasks/ returns no semantic duplicate"

  - id: task-is-atomic
    check: "Task represents a single atomic operation, not a multi-phase workflow"
    type: blocking
    validation: "If 3+ phases or 2+ agents needed, use workflow instead"
```

---

## Task Anatomy (8 Required Fields)

```yaml
anatomy_checks:
  - id: field-task-name
    check: "task_name field present in Verb + Object format (Title Case)"
    type: blocking
    pattern: "^[A-Z][a-z]+ [A-Z].*$"
    examples: ["Analyze Briefing", "Create Project Setup", "Validate Quality Gate"]

  - id: field-status
    check: "status field present with valid enum value"
    type: blocking
    valid_values: ["pending", "in_progress", "completed"]

  - id: field-responsible-executor
    check: "responsible_executor field identifies who or what executes the task"
    type: blocking
    validation: "Non-empty string referencing an agent, role, or worker"

  - id: field-execution-type
    check: "execution_type field uses valid enum from decision tree"
    type: blocking
    valid_values: ["Human", "Agent", "Hybrid", "Worker"]
    decision_tree: |
      Creative judgment or relationships -> Human (HO-EP-001)
      Pattern recognition or content generation -> Agent (HO-EP-002)
      AI drafts + human approves -> Hybrid (HO-EP-003)
      Deterministic API/file operations -> Worker (HO-EP-004)

  - id: field-input
    check: "input field is a YAML array with 1+ specific items"
    type: blocking
    validation: "typeof(input) == array AND len(input) >= 1"

  - id: field-output
    check: "output field is a YAML array with 1+ specific items"
    type: blocking
    validation: "typeof(output) == array AND len(output) >= 1"

  - id: field-action-items
    check: "action_items field is a YAML array with 1+ executable steps"
    type: blocking
    validation: "Each item starts with an action verb"

  - id: field-acceptance-criteria
    check: "acceptance_criteria field is a YAML array with 1+ testable criteria"
    type: blocking
    validation: "Each criterion is answerable with YES/NO"
```

---

## Executor Type Decision Tree

```yaml
executor_checks:
  - id: executor-matches-complexity
    check: "execution_type matches task complexity and requirements"
    type: blocking
    validation: |
      Human: requires judgment, creativity, stakeholder relationships
      Agent: analysis-heavy, pattern recognition, content generation
      Hybrid: AI drafts + human validates, learning phase
      Worker: deterministic, APIs, file ops, no variation

  - id: executor-time-alignment
    check: "estimated_time aligns with execution_type typical ranges"
    type: recommended
    ranges:
      Worker: "0-0.5h"
      Agent: "0.5-2h"
      Hybrid: "1-4h"
      Human: "1-8h"

  - id: executor-fallback
    check: "Critical tasks define a fallback executor"
    type: recommended
    validation: "fallback_executor field exists for critical tasks"
```

---

## Input/Output Governance

```yaml
io_checks:
  - id: inputs-are-specific
    check: "Each input is a specific identifiable artifact, not vague"
    type: blocking
    anti_patterns: ["various documents", "relevant data", "all information"]

  - id: outputs-are-verifiable
    check: "Each output is a specific deliverable with clear format"
    type: blocking
    anti_patterns: ["improvements", "results", "updates"]

  - id: output-persistence
    check: "output_persistence field classifies output as canonical_workspace or transient_output"
    type: blocking
    validation: "output_persistence in [canonical_workspace, transient_output]"

  - id: output-path-governance
    check: "Output path matches persistence classification"
    type: blocking
    validation: |
      canonical_workspace -> workspace/businesses/{business}/
      transient_output -> .aiox/squad-runtime/{squad}/{business}/
      HIGH-VALUE output in .aiox/squad-runtime/ -> VETO
```

---

## Veto Conditions

```yaml
veto_checks:
  - id: veto-conditions-documented
    check: "Task documents conditions that would cause rejection of output"
    type: recommended
    validation: "veto_conditions section exists with 1+ conditions"

  - id: veto-has-remediation
    check: "Each veto condition has a remediation path"
    type: recommended
    validation: "Each veto entry has fix or remediation field"
```

---

## Registration and Integration

```yaml
registration_checks:
  - id: task-in-config
    check: "Task is registered in squad config.yaml or referenced by an agent"
    type: blocking
    validation: "Task file referenced in agents/commands or workflows"

  - id: no-orphan
    check: "Task is not orphaned (referenced by at least 1 agent or workflow)"
    type: blocking
    validation: "grep task filename across agents/ and workflows/ returns 1+ match"

  - id: template-format
    check: "Task file follows squad template format (YAML frontmatter or consistent structure)"
    type: blocking
    validation: "File structure matches tasks/ conventions in target squad"

  - id: dependencies-exist
    check: "All files referenced in task dependencies exist"
    type: blocking
    validation: "Each path in dependencies[] resolves to existing file"
```

---

## Governance Framework Compliance

```yaml
fw_checks:
  - id: artifact-contract-match
    check: "If task produces an artifact, it maps to a declared artifact_contract in config.yaml"
    type: recommended
    validation: "output artifact_id exists in config.yaml artifact_contracts[]"

  - id: mode-alignment
    check: "Task aligns with one of the squad's declared supported_modes"
    type: recommended
    valid_modes: ["CRIAR", "RESOLVER", "GERENCIAR", "ENTENDER", "VALIDAR", "CONFIGURAR", "PLANEJAR", "EXPLORAR"]
```

---

## Scoring

| Score | Result | Action |
|-------|--------|--------|
| 100% Blocking + 80% Recommended | EXCELLENT | Task ready for deployment |
| 100% Blocking + 50% Recommended | GOOD | Deploy with documented gaps |
| 100% Blocking + <50% Recommended | CONDITIONAL | Improve before production use |
| <100% Blocking | FAIL | Fix blocking items before deployment |

---

**Created:** 2026-03-26
**Task Reference:** tasks/create-task.md
**Related:** checklists/task-anatomy-checklist.md (field-level validation details)
