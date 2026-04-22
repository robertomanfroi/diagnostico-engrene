# Task: Validate Squad — Preflight

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-preflight` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: validate-squad-preflight
name: "Validate Squad Preflight"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Run deterministic worker scripts and collect structural signals. Blocking gate before any semantic analysis."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::validate_squad_preflight
Output: artifact::validate_squad_preflight
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Execute all deterministic worker scripts against a squad directory, collect structural signals (inventory, naming, dependencies, checklists, coherence, scoring, security), and evaluate blocking conditions. This is the mandatory first step -- no subsequent validation phase may proceed without a successful preflight.

## Prerequisites

- [ ] Squad directory exists at `squads/{squad_name}/`
- [ ] `config.yaml` exists in squad root
- [ ] Worker scripts available in `squads/squad-creator/scripts/`

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
    description: "Name of the squad to validate"
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
    description: "Override default squad path"
```

## Workflow / Steps

### Step 1: Run Worker Scripts

**Option A: Atomic scripts (recommended -- deterministic phases 0-3, no Claude required)**

```bash
# Phases 0-2: Structure validation (type detection, structure, coverage)
python3 squads/squad-creator/scripts/validate-squad-structure.py squads/{squad_name}/ --output json > /tmp/preflight-structure.json

# Phase 3: Quality analysis (task anatomy, AC, workflows, monolithic files)
python3 squads/squad-creator/scripts/validate-squad-quality.py squads/{squad_name}/ --output json > /tmp/preflight-quality.json
```

These are the deterministic phases (0-3). No Claude CLI required. Pure static analysis.

**Option B: All-in-one orchestrator (includes Claude deep review in phases 4-6)**

```bash
bash squads/squad-creator/scripts/validate-squad.sh {squad_name} --json > /tmp/preflight-results.yaml
```

**Option C: Full modular scripts (for debugging)**

```bash
cd /path/to/project

# 1. INVENTORY: What exists in the squad?
python3 squads/squad-creator/scripts/inventory.py squads/{squad_name}/ --output json > /tmp/preflight-inventory.json

# 2. NAMING: Are conventions followed?
python3 squads/squad-creator/scripts/naming_validator.py squads/{squad_name}/ --output json > /tmp/preflight-naming.json

# 3. DEPENDENCIES: Are all references valid?
python3 squads/squad-creator/scripts/dependency_check.py squads/{squad_name}/ --output json > /tmp/preflight-deps.json

# 4. CHECKLISTS: Are checklists well-formed?
python3 squads/squad-creator/scripts/checklist_validator.py squads/{squad_name}/checklists/ --all --output json > /tmp/preflight-checklists.json

# 5. COHERENCE: Are heuristics/axiomas consistent? (squad-creator only)
python3 squads/squad-creator/scripts/coherence-validator.py --output json > /tmp/preflight-coherence.json

# 6. SCORING: Calculate weighted quality score
python3 squads/squad-creator/scripts/scoring.py squads/{squad_name}/ --output json > /tmp/preflight-scoring.json

# 7. SECURITY: Are there any secrets/credentials exposed?
python3 squads/squad-creator/scripts/security_scanner.py squads/{squad_name}/ --output json > /tmp/preflight-security.json
```

> Note (Base/Pro boundary): `coherence-validator.py` and `scoring.py` are Base adapters. With `squad-creator-pro` installed they delegate to Pro scripts. Without Pro they return `status: SKIPPED_PRO_ONLY`, `blocking_issues: 0`.

### Step 2: Evaluate Blocking Conditions

```yaml
blocking_checks:
  - inventory.json -> squad_exists == false -> BLOCK
  - naming.json -> violations.count > 5 -> BLOCK
  - deps.json -> broken_references.count > 0 -> BLOCK (fix refs first)
  - checklists.json -> invalid_files > 3 -> WARN (continue with warning)
  - coherence.json -> blocking_issues > 0 -> BLOCK (squad-creator only)
  - security.json -> critical_count > 0 -> BLOCK (fix secrets first!)
```

**IF ANY blocking issue found:** STOP. Report issues. Reviewer CLI cannot override these facts.

**IF ALL pass:** Preflight succeeds. Downstream tasks may proceed.

### Step 3: Persist Runtime State

Write state to canonical path:

```
.aiox/squad-runtime/validate-squad/{squad_name}/state.json
```

- If state file does not exist: start from `init` and create state at canonical path.
- If state is corrupted: stop validation, preserve corrupted file as evidence, restart from `init` after manual fix.
- Never use local legacy validate-state files as source of truth.

## Output

```yaml
output:
  file: "/tmp/preflight-results.yaml"
  state: ".aiox/squad-runtime/validate-squad/{squad_name}/state.json"
  schema:
    status: "PASS | BLOCK"
    blocking_issues: []
    warnings: []
    metrics:
      agents_count: N
      tasks_count: N
      workflow_count: N
      total_lines: N
    security:
      critical_count: N
      warning_count: N
    structure:
      config_valid: true/false
      entry_agent_exists: true/false
      broken_references: N
```

## Acceptance Criteria

- [ ] At least one worker script execution path produces `/tmp/preflight-results.yaml`
- [ ] All 7 script categories are represented in output (or marked SKIPPED with reason)
- [ ] Blocking conditions are evaluated and clearly reported
- [ ] Runtime state is persisted at canonical path
- [ ] No manual `ls`/`grep`/`wc` used to collect data that scripts already compute

## Veto Conditions

- `/tmp/preflight-results.yaml` does not exist after execution -> VETO downstream tasks
- Any blocking check triggers -> VETO downstream tasks (except deep-review which is skipped)
- Script execution fails with non-zero exit -> VETO (fix script, do not proceed manually)

## Related Documents

- `validate-squad.md` (parent composed task)
- `validate-squad-classify.md` (uses preflight signals for type detection + compliance)
- `scripts/validate-squad.sh` (all-in-one worker)
- `scripts/lib/validate-runtime-state.cjs` (canonical path writer)
- `docs/RFC-001-deterministic-refactoring.md`
