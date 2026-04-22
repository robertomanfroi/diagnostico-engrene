# Task: Validate Squad — Classification & Compliance

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: validate-squad-classify
name: "Validate Squad Classification & Compliance"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Detect squad type (Expert/Pipeline/Hybrid/Operational) from structural signals, load type-specific requirements, and validate governance framework compliance in a single pass."
accountability:
  human: squad-operator
  scope: full
domain: Strategic

```


<!-- SINKRA_CONTRACT -->
Domain: `Strategic`
atomic_layer: Atom
Input: request::validate_squad_classify
Output: artifact::validate_squad_classify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Classify the squad by type using a deterministic detection algorithm (dominant signals, scoring, tie-breaking), then validate governance framework compliance (artifact_contracts, bu_mapping, supported_modes, agnosticism) against the detected type's requirements. Both operations score on preflight data -- they share the same input surface and belong in the same cognitive unit.

**Why merged:** Type detection and compliance scoring are two lenses on the same preflight data. Splitting them forced an artificial handoff with zero new information between tasks.

## Prerequisites

- [ ] Preflight completed successfully (`validate-squad-preflight`)
- [ ] Preflight results available with signal data
- [ ] `data/squad-type-definitions.yaml` accessible
- [ ] Squad `config.yaml` exists and is valid YAML

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
  type_override:
    type: string
    required: false
    description: "Force squad type: expert, pipeline, hybrid, operational"
  preflight_results:
    type: object
    required: true
    description: "Output from validate-squad-preflight"
  config:
    type: file
    required: true
    path: "{squad_path}/config.yaml"
```

## Workflow / Steps

### Step 1: Collect Signals (from preflight data)

Read signal values from preflight results. Do NOT re-collect manually.

```yaml
signal_collection:
  agents_count: "N (from preflight)"
  voice_dna_count: "N (agents containing 'voice_dna:')"
  voice_dna_percentage: "voice_dna_count / agents_count * 100"
  workflow_count: "N (.yaml files in workflows/)"
  has_heuristic_ids: "true/false (patterns PV_|SC_|HO_ present)"
  tasks_count: "N (.md files in tasks/, recursive)"
  has_real_person_names: "true/false (e.g. gary-halbert, eugene-schwartz)"
  has_tier_organization: "true/false ('tier:' or 'Tier 0' in config/agents)"
```

### Step 2: Detect Squad Type

If `type_override` is provided, skip detection and use the override directly. Log that override was applied.

#### 2a: Check Dominant Signals

Dominant signals are EXCLUSIVE -- only ONE type has them. If triggered, skip scoring.

```yaml
dominant_signals:
  expert_override:
    condition: "voice_dna_percentage >= 50"
    action: "TYPE = Expert (OVERRIDE)"
    rationale: "Pipeline and Hybrid squads NEVER have voice_dna in agents."

  hybrid_override:
    condition: "has_heuristic_ids == true"
    action: "TYPE = Hybrid (OVERRIDE)"
    rationale: "Only Hybrid squads use heuristic IDs (PV_*, SC_*, HO_*)."
```

#### 2b: Scoring Algorithm (only if no dominant signal)

```yaml
detection_algorithm:
  expert_score: 0
  pipeline_score: 0
  hybrid_score: 0

  # EXCLUSIVE signals - HIGH weight
  if voice_dna_percentage >= 50:  expert_score += 5
  if has_heuristic_ids:           hybrid_score += 5
  if has_real_person_names:       expert_score += 3

  # SHARED signals - LOW weight
  if agents_count >= 5:           expert_score += 1
  if has_tier_organization:       expert_score += 1
  if workflow_count > 0:          pipeline_score += 2
  if tasks_count > agents_count * 3: pipeline_score += 1

  # NEGATIVE weights
  if voice_dna_percentage >= 50:  pipeline_score -= 3
  if has_heuristic_ids:           pipeline_score -= 2

  # Shared neutral signals
  if has_orchestrator_agent:      pipeline_score += 1
  if has_persona_profile_pattern: hybrid_score += 2

  # Determine winner
  detected_type: max(expert_score, pipeline_score, hybrid_score)

  # Tie-breaking
  if tie:
    if has_real_person_names: "expert"
    elif workflow_count > 0: "pipeline"
    else: "pipeline"  # default
```

### Step 3: Load Type-Specific Requirements

```yaml
load_requirements:
  file: "data/squad-type-definitions.yaml"
  section: "squad_types.{detected_type}"
  output:
    required_components: [...]
    optional_components: [...]
    veto_conditions: [...]
    benchmarks: {...}
```

### Step 4: Validate Governance Compliance

#### 4a: Check artifact_contracts (REQUIRED)

```yaml
artifact_contracts_check:
  id: "FW-AC-001"
  severity: BLOCKING
  check: "config.yaml contains artifact_contracts[] array"
  validation:
    - "artifact_contracts[] exists and is non-empty"
    - "Each contract has: artifact_id, template_path, lifecycle_states"
    - "template_path references a file that exists in templates/"
    - "lifecycle_states is a valid subset of [draft, validated, approved, superseded, archived]"
  on_fail: "BLOCK - artifact_contracts missing or malformed"
```

#### 4b: Check bu_mapping (RECOMMENDED)

```yaml
bu_mapping_check:
  id: "FW-BU-001"
  severity: WARNING
  check: "config.yaml contains bu_mapping field"
  validation:
    - "bu_mapping references a valid BU from bu-map.yaml"
    - "Referenced BU exists in workspace or data layer"
  on_missing: "WARNING - bu_mapping not declared (recommended)"
```

#### 4c: Check supported_modes (RECOMMENDED)

```yaml
supported_modes_check:
  id: "FW-SM-001"
  severity: WARNING
  check: "config.yaml contains supported_modes[] array"
  validation:
    - "Each mode is one of: CRIAR, RESOLVER, GERENCIAR, ENTENDER, VALIDAR, CONFIGURAR, PLANEJAR, EXPLORAR"
    - "At least 1 mode declared"
    - "Declared modes align with squad capabilities"
  on_missing: "WARNING - supported_modes not declared (recommended)"
```

#### 4d: Check Lifecycle State Coverage

```yaml
lifecycle_check:
  id: "FW-LC-001"
  severity: WARNING
  check: "Artifact lifecycle states are properly managed"
  validation:
    - "Templates referenced in artifact_contracts exist"
    - "Templates contain lifecycle state transitions"
    - "Tasks that produce artifacts reference the correct template"
    - "Artifacts flow: draft -> validated -> approved (minimum viable lifecycle)"
  on_fail: "WARNING - Lifecycle state coverage incomplete"
```

### Step 5: Check Agnosticism (NON-NEGOTIABLE)

```yaml
agnosticism_check:
  id: "FW-AG-001"
  severity: BLOCKING
  check: "Squad contains no business-specific data"
  validation:
    - "No product names, prices, or client data in squad files"
    - "No business-specific URLs or endpoints hardcoded"
    - "Templates use placeholders, not concrete values"
    - "Data files contain frameworks/rules, not business instances"
  on_fail: "BLOCK - Squad contains business-specific data"
```

### Step 6: Calculate Compliance Score

```yaml
compliance_scoring:
  artifact_contracts: "present + valid = 30 points"
  bu_mapping: "present + valid = 15 points"
  supported_modes: "present + valid = 15 points"
  lifecycle_coverage: "templates exist + transitions defined = 20 points"
  agnosticism: "no business data = 20 points"
  total: "100 points"

  interpretation:
    90-100: "FULL COMPLIANCE"
    70-89: "PARTIAL COMPLIANCE - recommended improvements"
    50-69: "LOW COMPLIANCE - required improvements"
    0-49: "NON-COMPLIANT - blocking"
```

## Output

```yaml
output:
  schema:
    # Type Detection
    detected_type: "expert | pipeline | hybrid | operational"
    confidence: 0.0-1.0
    detection_method: "dominant_signal | scoring | override"
    signals:
      agents_count: N
      voice_dna_present: true/false
      voice_dna_percentage: N
      has_workflow: true/false
      has_heuristic_ids: true/false
      task_agent_ratio: N
    requirements_loaded: true/false
    required_components: [...]
    veto_conditions: [...]

    # Governance Compliance
    compliance_score: 0-100
    compliance_level: "FULL | PARTIAL | LOW | NON_COMPLIANT"
    checks:
      artifact_contracts:
        status: "PASS | FAIL | MISSING"
        count: N
        valid: N
      bu_mapping:
        status: "PASS | MISSING"
        value: "bu-name | null"
      supported_modes:
        status: "PASS | MISSING"
        modes: [...]
      lifecycle:
        status: "PASS | PARTIAL | FAIL"
        coverage: "N%"
      agnosticism:
        status: "PASS | FAIL"
        violations: [...]
    blocking_issues: []
    warnings: []
```

## Acceptance Criteria

- [ ] Type is detected deterministically from structural signals
- [ ] Dominant signals short-circuit the scoring algorithm
- [ ] Override parameter bypasses detection entirely
- [ ] Type-specific requirements are loaded from `squad-type-definitions.yaml`
- [ ] Confidence score reflects detection method quality
- [ ] artifact_contracts validated against template existence
- [ ] bu_mapping validated against known BU definitions
- [ ] supported_modes validated against canonical mode list
- [ ] Lifecycle states checked for completeness
- [ ] Agnosticism check catches business-specific data
- [ ] Compliance score calculated correctly from weighted checks
- [ ] Blocking issues prevent PASS in parent validation

## Veto Conditions

- Squad does not exist -> VETO (should be caught by preflight)
- No agents found -> VETO (cannot determine type without agents)
- `squad-type-definitions.yaml` missing -> VETO (cannot load requirements)
- artifact_contracts missing entirely -> BLOCK (governance framework REQUIRED field)
- Business-specific data found in squad -> BLOCK (agnosticism violation)

## Related Documents

- `validate-squad.md` (parent composed task)
- `validate-squad-preflight.md` (provides signal data)
- `data/squad-type-definitions.yaml` (type definitions and requirements)
- `governance/composition-rules.yaml` (canonical composition rules)
- `data/process-token-map.yaml` (contrato local de tokens do processo)
- `.claude/rules/squads.md` (squad structure rules)
- `.claude/rules/workspace-docs.md` (agnosticism rules)
