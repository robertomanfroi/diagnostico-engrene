# Task: Scan Environment for Available Tools

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools-scan` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: discover-tools-scan
name: "Scan Environment for Available Tools"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: >
  Validates domain context from canonical artifacts, scans internal squad
  infrastructure, and identifies capability gaps before external search.
  Corresponds to Phases -2, -1, and 0 of the original discover-tools pipeline.
accountability:
  human: squad-operator
  scope: review_only

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::discover_tools_scan
Output: artifact::discover_tools_scan
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Establish verified domain scope and scan the internal environment (squad structure,
configured MCP servers, local skills, existing squads) to build a complete picture
of what capabilities already exist and what gaps remain for external discovery.

## Prerequisites

- [ ] squad-chief agent is active
- [ ] Domain and use cases clearly defined
- [ ] Write permissions for `.aiox/squad-runtime/discovery/{domain}/`

## Inputs

| Parameter | Type | Required | Description | Example |
|-----------|------|----------|-------------|---------|
| `domain` | string | Yes | Squad domain | `"copywriting"` |
| `use_cases` | list | Yes | Key squad use cases | `["sales pages", "email sequences"]` |
| `existing_tools` | list | No | Tools already in use | `["exa", "web_fetch"]` |
| `capability_gaps` | list | No | Known capability gaps | `["pdf_processing"]` |
| `scope_hint` | string | No | Extra clarification for ambiguous domains | `"rules extraction from code"` |

## Workflow

### Step 1: Domain Context Validation (PHASE -2)

Resolve scope from canonical artifacts -- never infer from slug/name alone.

```yaml
scope_resolution:
  canonical_sources_priority:
    - "squads/{domain}/squad.yaml"
    - "squads/{domain}/config.yaml"
    - "squads/{domain}/README.md"
    - "{registry_path}"
    - "related squad workflows/tasks/agents"

  rules:
    - "DO NOT infer scope from slug/name alone"
    - "Collect explicit domain/purpose/use-cases evidence"
    - "Mark unresolved or conflicting sources explicitly"
```

Build an evidence pack with `source_path`, `extracted_scope_statement`, and `status`.

Enforce ambiguity gate:
- PASS when declared_domain and declared_purpose are explicit, no contradictions.
- FAIL when scope derived only from name/slug, canonical files missing/conflicting, or confidence is low.
- On FAIL: HALT discovery and ask user for clarification.

### Step 2: Internal Infrastructure Scan (PHASE -1)

```yaml
internal_scan:
  scan_paths:
    - "squads/{domain}/config.yaml"
    - "squads/{domain}/agents/"
    - "squads/{domain}/tasks/"
    - "squads/{domain}/workflows/"
    - "squads/{domain}/data/"
    - ".claude/settings.local.json"
    - ".claude/settings.json"

  extract:
    - declared_tools
    - agent_capabilities
    - task_dependencies
    - workflow_integrations
```

Map internal coverage per use case: `covered`, `partially_covered`, `not_covered`.

### Step 3: Capability Gap Analysis (PHASE 0)

For each use case, derive required capabilities across four dimensions:
input, processing, output, enhancement.

Check existing tool coverage from squad config and configured MCPs.

Scan local skills (`.claude/skills/*/SKILL.md`) and squads (`squads/*/config.yaml`).
Classify matches as COVERS, ADAPTABLE, or UNRELATED.

Prioritize gaps using: `impact * 0.4 + frequency * 0.3 + user_dependency * 0.3`.

## Output

```yaml
scan_output:
  scope_status: "verified|partial|unverified"
  canonical_scope:
    domain: ""
    purpose: ""
  evidence_paths: []
  contradictions_found: []
  requires_user_clarification: true/false
  internal_capabilities_found: N
  covered_by_internal: N
  partial_internal: N
  external_only_gaps: N
  local_skills_coverage:
    skills_scanned: N
    squads_scanned: N
    covers: []
    adaptable: []
    gaps: []
  prioritized_gaps:
    - capability: ""
      priority: 0.0
      search_queries: []
  external_search_scope:
    required: []
    optional: []
```

Output file: `.aiox/squad-runtime/discovery/{domain}/scan-results.yaml`

## Acceptance Criteria

- [ ] Domain intent validated from canonical artifacts before any external search
- [ ] No scope decision based only on squad/domain name
- [ ] Internal structure fully scanned before defining external scope
- [ ] External search scope derived exclusively from internal gaps
- [ ] All capability gaps scored and prioritized
- [ ] Local skills and squads scanned for reuse opportunities

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-SCAN-001"
    condition: "Canonical domain context unresolved or contradictory"
    trigger: "Ambiguity gate (Step 1)"
    block_behavior: "BLOCK entire pipeline; require clarification first"
```

## Related Documents

- `discover-tools.md` -- Orchestrator (parent task)
- `discover-tools-classify.md` -- Next task in pipeline
- `data/quality-dimensions-framework.md` -- Quality scoring reference
- `protocols/ai-first-governance.md` -- Canonical scope validation

---

_Task Version: 1.0.0_
_Extracted from: discover-tools.md v3.0 (Phases -2, -1, 0)_
