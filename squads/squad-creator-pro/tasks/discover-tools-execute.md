<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: discover-tools-execute
  task_name: Discover Tools Execute (Consolidated Pipeline Proxy)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 45m
  domain: Operational
  input:
  - domain (string, required)
  - use_cases (list, required)
  - existing_tools (list, optional)
  - capability_gaps (list, optional)
  - budget_tier (enum, optional)
  - priority_capabilities (list, optional)
  - search_depth (enum, optional)
  - scope_hint (string, optional)
  output:
  - '.aiox/squad-runtime/discovery/{domain}/scan-results.yaml'
  - '.aiox/squad-runtime/discovery/{domain}/classified-tools.yaml'
  - '.aiox/squad-runtime/discovery/{domain}/evaluated-tools.yaml'
  - '.aiox/squad-runtime/discovery/{domain}/recommendations.yaml'
  - '.aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md'
  - '.aiox/squad-runtime/discovery/{domain}/capability-tools.yaml'
  - '.aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md'
  action_items:
  - 'Step 1: Scan -- delegate to squad-creator base scan task'
  - 'Step 2: Classify -- delegate to squad-creator base classify task'
  - 'Step 3: Evaluate -- delegate to squad-creator base evaluate task'
  - 'Step 4: Recommend -- delegate to squad-creator base recommend task'
  - 'Step 5: Report -- delegate to squad-creator base report task'
  acceptance_criteria:
  - O pro não mantém uma segunda implementação de nenhuma fase do pipeline
  - Cada step delega ao owner canônico no squad-creator base
  - Os artefatos locais do pro (tool-registry, internal-infrastructure-library) entram como overlay
  - Todos os outputs intermediários e finais são produzidos nos paths esperados
  - O scoring é herdado do base (nenhuma lógica paralela de score)
  - A recomendação é determinada pelo owner canônico do base
  - A geração dos artefatos finais continua centralizada no base
  - O workflow do pro possui owner atômico explícito em cada fase
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
  coherence_threshold: 0.95
  error_behavior: raise
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Discover Tools Execute (Consolidated Pipeline Proxy)

**Task ID:** discover-tools-execute
**Version:** 1.0.0
**Purpose:** Execute the complete tool discovery pipeline (scan, classify, evaluate, recommend, report) by delegating each phase to the canonical owner in `squad-creator` base
**Executor:** Agent (@squad-chief)
**Mode:** Delegation-first
**Quality Standard:** Herdado das tasks base em `squads/squad-creator/tasks/`

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **Executor** | Agent (@squad-chief) |
| **Inputs** | domain, use_cases, existing_tools, capability_gaps, budget_tier, priority_capabilities, search_depth, scope_hint |
| **Outputs** | scan-results, classified-tools, evaluated-tools, recommendations, tool-discovery-report, capability-tools, tool-integration-plan |
| **Completion Criteria** | All 5 pipeline steps delegated and all outputs produced in `.aiox/squad-runtime/discovery/{domain}/` |
| **Guardrails** | No parallel logic -- all execution delegated to squad-creator base tasks |

---

## Purpose

This consolidated proxy replaces the 5 individual wrapper stubs (discover-tools-scan, discover-tools-classify, discover-tools-evaluate, discover-tools-recommend, discover-tools-report) that existed as pure delegation wrappers.

Each step delegates to the canonical owner in `squad-creator` base. The `squad-creator-pro` adds only:

1. Pro overlay context (tool-registry, internal-infrastructure-library)
2. Pipeline sequencing within a single task
3. Output reconciliation

**Non-negotiable rule:** The `squad-creator-pro` MUST NOT maintain parallel implementations of any pipeline phase.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `domain` | string | Yes | Dominio ou squad alvo |
| `use_cases` | list | Yes | Casos de uso principais |
| `existing_tools` | list | No | Ferramentas ja conhecidas |
| `capability_gaps` | list | No | Gaps ja percebidos |
| `budget_tier` | enum | No | `free_only`, `low_cost`, `enterprise` (default: `low_cost`) |
| `priority_capabilities` | list | No | Capacidades a priorizar |
| `search_depth` | enum | No | `quick`, `standard`, `exhaustive` (default: `standard`) |
| `scope_hint` | string | No | Clarificacao para dominios ambiguos |

---

## Preconditions

- [ ] `squads/squad-creator/tasks/discover-tools-scan.md` exists
- [ ] `squads/squad-creator/tasks/discover-tools-classify.md` exists
- [ ] `squads/squad-creator/tasks/discover-tools-evaluate.md` exists
- [ ] `squads/squad-creator/tasks/discover-tools-recommend.md` exists
- [ ] `squads/squad-creator/tasks/discover-tools-report.md` exists
- [ ] `data/internal-infrastructure-library.yaml` exists in squad-creator-pro
- [ ] `data/tool-registry.yaml` exists in squad-creator-pro

---

## Workflow

### Step 1: Scan -- Structural Discovery

Delegate structural scanning of tools to the base canonical task.

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/discover-tools-scan.md"
  payload:
    - domain
    - use_cases
    - existing_tools
    - capability_gaps
    - scope_hint
  overlay_inputs:
    - internal_infrastructure_library: "data/internal-infrastructure-library.yaml"
    - tool_registry: "data/tool-registry.yaml"
  prohibition:
    - "Do NOT reimplement scan logic inside squad-creator-pro"
  output: ".aiox/squad-runtime/discovery/{domain}/scan-results.yaml"
```

### Step 2: Classify -- Candidate Classification

Delegate classification of discovered tool candidates to the base canonical task.

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/discover-tools-classify.md"
  payload:
    - scan_output: "{step_1_output}"
    - domain
    - use_cases
    - budget_tier
  overlay_rules:
    - "Honor external-only gaps produced by the pro scan step"
    - "Keep pro-local exclusions and internal-first decisions"
  prohibition:
    - "Do NOT fork classification logic in squad-creator-pro"
  output: ".aiox/squad-runtime/discovery/{domain}/classified-tools.yaml"
```

### Step 3: Evaluate -- Scoring and Compatibility

Delegate scoring and compatibility evaluation to the base canonical task.

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/discover-tools-evaluate.md"
  payload:
    - classified_tools: "{step_2_output}"
    - prioritized_gaps: "{from_step_1}"
    - budget_tier
  prohibition:
    - "Do NOT fork tool scoring in squad-creator-pro"
  output: ".aiox/squad-runtime/discovery/{domain}/evaluated-tools.yaml"
```

### Step 4: Recommend -- Prioritization and Decision

Delegate recommendation and prioritization to the base canonical task.

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/discover-tools-recommend.md"
  payload:
    - evaluated_tools: "{step_3_output}"
    - scan_output: "{step_1_output}"
    - domain
  prohibition:
    - "Do NOT keep a second impact-vs-effort matrix in squad-creator-pro"
  output: ".aiox/squad-runtime/discovery/{domain}/recommendations.yaml"
```

### Step 5: Report -- Final Artifact Generation

Delegate final report and artifact generation to the base canonical task.

```yaml
delegate_to_base:
  task: "squads/squad-creator/tasks/discover-tools-report.md"
  payload:
    - recommend_output: "{step_4_output}"
    - scan_output: "{step_1_output}"
    - domain
  prohibition:
    - "Do NOT duplicate report generation logic in squad-creator-pro"
  outputs:
    - ".aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md"
    - ".aiox/squad-runtime/discovery/{domain}/capability-tools.yaml"
    - ".aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md"
```

---

## Output

```yaml
output:
  name: discover_tools_pipeline_result
  format: yaml
  structure:
    pipeline_steps:
      scan:
        delegated_task: "squads/squad-creator/tasks/discover-tools-scan.md"
        output: ".aiox/squad-runtime/discovery/{domain}/scan-results.yaml"
      classify:
        delegated_task: "squads/squad-creator/tasks/discover-tools-classify.md"
        output: ".aiox/squad-runtime/discovery/{domain}/classified-tools.yaml"
      evaluate:
        delegated_task: "squads/squad-creator/tasks/discover-tools-evaluate.md"
        output: ".aiox/squad-runtime/discovery/{domain}/evaluated-tools.yaml"
      recommend:
        delegated_task: "squads/squad-creator/tasks/discover-tools-recommend.md"
        output: ".aiox/squad-runtime/discovery/{domain}/recommendations.yaml"
      report:
        delegated_task: "squads/squad-creator/tasks/discover-tools-report.md"
        outputs:
          - ".aiox/squad-runtime/discovery/{domain}/tool-discovery-report.md"
          - ".aiox/squad-runtime/discovery/{domain}/capability-tools.yaml"
          - ".aiox/squad-runtime/discovery/{domain}/tool-integration-plan.md"
    domain: "{domain}"
    execution_mode: "consolidated-proxy"
    status: "delegated"
```

---

## Acceptance Criteria

- [ ] O pro nao mantem uma segunda implementacao de nenhuma fase do pipeline
- [ ] Cada step delega ao owner canonico no squad-creator base
- [ ] Os artefatos locais do pro (tool-registry, internal-infrastructure-library) entram como overlay
- [ ] Todos os outputs intermediarios e finais sao produzidos nos paths esperados
- [ ] O scoring e herdado do base (nenhuma logica paralela de score)
- [ ] A recomendacao e determinada pelo owner canonico do base
- [ ] A geracao dos artefatos finais continua centralizada no base
- [ ] O workflow do pro possui owner atomico explicito em cada fase

---

## Veto Conditions

- Any base task in `squads/squad-creator/tasks/discover-tools-*.md` does not exist
- `domain` not provided
- `use_cases` not provided

---

## Related Documents

- `squads/squad-creator/tasks/discover-tools-scan.md` -- canonical owner (scan)
- `squads/squad-creator/tasks/discover-tools-classify.md` -- canonical owner (classify)
- `squads/squad-creator/tasks/discover-tools-evaluate.md` -- canonical owner (evaluate)
- `squads/squad-creator/tasks/discover-tools-recommend.md` -- canonical owner (recommend)
- `squads/squad-creator/tasks/discover-tools-report.md` -- canonical owner (report)
- `workflows/wf-discover-tools.yaml` -- workflow consumer in pro
- `data/tool-registry.yaml` -- tool catalog and memory
- `data/internal-infrastructure-library.yaml` -- pro infrastructure hints

---

_Task Version: 1.0.0_
_Role: consolidated pipeline proxy replacing 5 individual wrapper stubs_
