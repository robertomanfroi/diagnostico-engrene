# Task: QA Check Compatibility

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qa-check-compatibility` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: qa-check-compatibility
name: QA Check Compatibility
category: qa-validation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Verify framework compatibility of a created component. Checks governance framework
  compliance, security scan (SEC-001 to SEC-018), AIOX convention adherence,
  and integration readiness with the broader ecosystem.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qa_check_compatibility
Output: artifact::qa_check_compatibility
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Ensure a created component is compatible with the governance framework, free of security vulnerabilities, and ready to integrate with the broader AIOX ecosystem. This catches framework-level issues that structure, schema, and reference checks do not cover.

## Prerequisites

- [ ] qa-check-structure has passed
- [ ] Component files are readable
- [ ] Security scan patterns available

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
```

## Workflow

### Step 1: Security Scan

**Duration:** < 10 seconds | **Blocking:** Yes (for HIGH severity)

Run comprehensive security pattern matching against all files in the component:

**HIGH severity (BLOCKING):**

| ID Range | Pattern | What It Catches |
|----------|---------|-----------------|
| SEC-001 to SEC-004 | API keys, tokens, bearer tokens, JWTs | Hardcoded credentials |
| SEC-005 to SEC-008 | AWS keys (AKIA...), cloud credentials | Cloud provider secrets |
| SEC-009 to SEC-010 | Private key headers (BEGIN.*PRIVATE KEY) | Leaked private keys |
| SEC-011 to SEC-012 | Database connection URIs with credentials | Exposed DB access |
| SEC-013 to SEC-015 | .env files, .pem files, credentials.json | Sensitive files committed |

**MEDIUM severity (WARNING):**

| ID Range | Pattern | What It Catches |
|----------|---------|-----------------|
| SEC-016 to SEC-018 | Code vulnerability patterns | Potential code issues |

**Scan command:**
```bash
grep -rE "(api[_-]?key|secret|password|bearer|jwt)\s*[:=]\s*['\"][^'\"${}]{8,}" {path} || true
grep -rE "AKIA[A-Z0-9]{16}" {path} || true
grep -rE "<db-url-pattern-redacted>" {path} || true
grep -rE "<private-key-pattern-redacted>" {path} || true
find {path} -name ".env*" -o -name "*.pem" -o -name "credentials*.json" 2>/dev/null || true
```

### Step 2: Governance Framework Compliance (Squads Only)

Check for governance framework required and recommended fields:

| Check | Required | Field |
|-------|----------|-------|
| Artifact contracts declared | RECOMMENDED | `artifact_contracts[]` in config.yaml |
| BU mapping present | RECOMMENDED | `bu_mapping` in config.yaml |
| Supported modes declared | RECOMMENDED | `supported_modes[]` in config.yaml |
| Lifecycle states defined | IF artifact_contracts | `lifecycle_states[]` per contract |

### Step 3: AIOX Convention Checks

| Check | Applies To | Rule |
|-------|------------|------|
| File names are kebab-case | All | No camelCase or PascalCase filenames |
| Agent IDs match filenames | Agents | `agent.id` == filename without extension |
| Task IDs match filenames | Tasks | Task ID == filename without extension |
| No business-specific data | All | Squad agnosticism -- no product names, prices, client data |

### Step 4: Integration Readiness

| Check | Description |
|-------|-------------|
| IDE sync compatibility | Can slash skills be synced to `.claude/skills/{squad}/{agent}/SKILL.md` |
| Activation shortcut format | Follows `/{squad}:{agent}` pattern |
| Template path resolution | Template paths resolve from squad root |

### Step 5: Compile Results

```yaml
compatibility_result:
  security:
    high_severity: N
    medium_severity: N
    findings:
      - id: "SEC-003"
        severity: "HIGH"
        file: "config.yaml"
        line: 42
        pattern: "service_token: 'sk-example-redacted-token'"
  fw_compliance:
    checks_run: N
    checks_passed: N
    warnings: [{field, message}]
  conventions:
    checks_run: N
    violations: [{file, rule, detail}]
  integration:
    checks_run: N
    issues: [{check, detail}]
  verdict: "PASS | FAIL"
  fail_reason: "..." # if verdict is FAIL
```

## Output

```yaml
output:
  name: compatibility_result
  type: object
  description: "Framework compatibility and security scan results"
  passed_to: qa-generate-report
```

## Acceptance Criteria

- [ ] All SEC-* patterns scanned against component files
- [ ] HIGH severity findings produce FAIL verdict
- [ ] MEDIUM severity findings produce warnings only
- [ ] Governance framework fields checked for squad components
- [ ] AIOX naming conventions verified
- [ ] No business-specific data in squad files
- [ ] Integration readiness checks completed

## Veto Conditions

| Condition | Action |
|-----------|--------|
| Any HIGH severity security finding | FAIL -- security vulnerability detected |
| Business-specific data in squad files | FAIL -- squad agnosticism violated |

## Related Documents

| Document | Purpose |
|----------|---------|
| `qa-after-creation.md` | Parent orchestrator task |
| `checklists/squad-checklist.md` | Security scan reference (Section 1.6) |
| `qa-generate-report.md` | Consumes this task's output |
