# Task: QA Check Schema

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-check-schema` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: qa-check-schema
name: QA Check Schema
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Validate schema conformance for config.yaml, task files, workflow files,
  and agent definitions. Ensures all fields match expected types, required
  sections are present, and values conform to allowed enums.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qa_check_schema
Output: artifact::qa_check_schema
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Verify that component files conform to their expected schema -- correct field names, proper types, valid enum values, and required sections. This goes beyond syntax (handled by qa-check-structure) to validate semantic correctness of the content shape.

## Prerequisites

- [ ] qa-check-structure has passed (structure_result.verdict == PASS)
- [ ] Component files are readable

## Inputs

```yaml
inputs:
  - name: created_component
    type: string
    required: true
    description: "Path to created component"

  - name: component_type
    type: enum
    required: true
    values: ["squad", "agent", "task", "workflow", "template"]
    description: "Type of component created"

  - name: structure_result
    type: object
    required: true
    source: qa-check-structure
    description: "Result from structure check (must be PASS)"
```

## Workflow

### Step 1: Select Schema Rules

Based on `component_type`, load the applicable schema rules:

**Squad (config.yaml):**

| Field | Type | Required | Allowed Values |
|-------|------|----------|----------------|
| pack.name | string | yes | kebab-case |
| pack.version | semver | yes | X.Y.Z |
| pack.description | string | yes | non-empty |
| pack.icon | string | no | single emoji |
| entry_agent | string | yes | must match an agent file |
| tested | boolean | yes | true/false |
| agents[] | array | yes | min 1 entry |
| agents[].id | string | yes | kebab-case |
| capabilities[] | array | no | -- |
| artifact_contracts[] | array | recommended | governance framework |

**Agent (.md files):**

| Section | Required | Validation |
|---------|----------|------------|
| YAML frontmatter or code block | yes | valid YAML |
| agent.name | yes | non-empty |
| agent.id | yes | kebab-case, matches filename |
| persona | yes | has role + style |
| commands[] | yes | min 1 command |
| activation-instructions | yes (entry agent) | non-empty block |

**Task (.md files):**

| Section | Required | Validation |
|---------|----------|------------|
| Task Anatomy table | yes | 5 fields: Task ID, Version, Status, Responsible Executor, Execution Type |
| Metadata code block | yes | valid YAML with id, name, category |
| Purpose | yes | non-empty |
| Inputs | yes | valid YAML with name, type, required |
| Workflow / Steps | yes | non-empty |
| Output | yes | defined |
| Acceptance Criteria | yes | min 1 criterion |

**Workflow (.yaml files):**

| Field | Required | Validation |
|-------|----------|------------|
| id | yes | kebab-case |
| version | yes | semver |
| phases[] | yes | min 1 phase |
| phases[].task | yes | references existing task file |

### Step 2: Run Schema Validation

For each applicable rule:
1. Read the target file
2. Parse the relevant section (YAML block, markdown table, heading)
3. Validate field presence, type, and value constraints
4. Record pass/fail per rule

### Step 3: Compile Results

```yaml
schema_result:
  checks_run: N
  checks_passed: N
  checks_failed: N
  failures:
    - field: "pack.version"
      expected: "semver format"
      actual: "v1"
      severity: "BLOCKING"
  warnings:
    - field: "artifact_contracts"
      message: "Recommended by governance framework but missing"
      severity: "WARN"
  verdict: "PASS | FAIL"
```

## Output

```yaml
output:
  name: schema_result
  type: object
  description: "Schema validation results with per-field detail"
  passed_to: qa-generate-report
```

## Acceptance Criteria

- [ ] Squad config.yaml validated against all required fields
- [ ] Agent files validated for persona, commands, activation-instructions
- [ ] Task files validated for Task Anatomy, Metadata, Purpose, Inputs, Output
- [ ] Workflow files validated for phases and task references
- [ ] governance framework fields (artifact_contracts) flagged as WARN if missing
- [ ] Blocking failures prevent overall PASS verdict
- [ ] Every check produces a traceable result entry

## Veto Conditions

| Condition | Action |
|-----------|--------|
| Required field missing with no default | FAIL -- schema non-conformant |
| Field value violates type constraint | FAIL -- invalid data |
| Entry agent ID does not match filename | FAIL -- naming convention violated |

## Related Documents

| Document | Purpose |
|----------|---------|
| `qa-after-creation.md` | Parent orchestrator task |
| `qa-check-structure.md` | Must pass before this task runs |
| `qa-generate-report.md` | Consumes this task's output |
| `data/quality-dimensions-framework.md` | Quality criteria reference |
