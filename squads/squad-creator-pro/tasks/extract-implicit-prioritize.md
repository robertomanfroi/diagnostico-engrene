---
task-id: extract-implicit-prioritize
name: "Prioritize Implicit Knowledge Findings"
version: 1.0.0
execution_type: Agent
model: Sonnet
model_rationale: "Prioritization uses structured ranking logic (Pareto, dependency analysis). Sonnet sufficient for ordering tasks."
haiku_eligible: false
estimated-time: 5 min
complexity: low

inputs:
  required:
    - analysis_findings: "Achados classificados por eixo (output de extract-implicit-analyze)"

outputs:
  primary:
    - prioritized_findings: "Top 5 criticos + lista completa ordenada por impacto"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit-prioritize
  task_name: Prioritize Implicit Knowledge Findings
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 5m
  domain: Operational
  input:
  - '{''analysis_findings'': ''Achados classificados por eixo (output de extract-implicit-analyze)''}'
  output:
  - '{''prioritized_findings'': ''Top 5 criticos + lista completa ordenada por impacto''}'
  action_items:
  - Consolidate All Findings
  - Apply Pareto-ao-Cubo Checkpoint
  - Sort by Impact Criteria
  - Extract Top 5
  - Detect Meta-Patterns
  acceptance_criteria:
  - All findings consolidated into single ranked list
  - Pareto-ao-Cubo checkpoint applied (not linear sorting)
  - Top 5 items selected with cross-axis representation when possible
  - Meta-patterns identified with supporting finding IDs
  - Sort criteria documented (impact > ease > dependencies)
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


# Task: Prioritize Implicit Knowledge Findings

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-implicit-prioritize` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-implicit` (orchestrator stub)
- **Sequence:** Phase 3 of 5
- **Previous Task:** `extract-implicit-analyze`
- **Next Task:** `extract-implicit-synthesize`

## Purpose

Take all findings from the 5-axis deep analysis and produce a prioritized ranking. Apply Pareto-ao-Cubo logic to ensure exponential-impact items surface first, not merely the easiest to fix.

## Prerequisites

- `extract-implicit-analyze` completed with `analysis_findings` output
- All CRITICO/ALTO findings have evidence anchors (VETO-EIM-003 passed)

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `analysis_findings` | Yes | All findings from the 5-axis analysis |

## Workflow / Steps

### Step 1: Consolidate All Findings

Merge all findings across the 5 axes into a single flat list with uniform fields:

```yaml
consolidated:
  - id: "P-001"
    axis: "premissa"
    nome: ""
    impacto: "CRITICO | ALTO | MEDIO"
    evidencia: ""
    pergunta_chave: ""
```

### Step 2: Apply Pareto-ao-Cubo Checkpoint

```yaml
checkpoint_pareto_priorizacao:
  question: "Top 5 criticos segue logica Pareto (impacto exponencial primeiro)?"
  if_pareto: "Priorizacao valida"
  if_linear: "Reordenar: CRITICO que desbloqueia outros primeiro"
  rationale: "Priorizar pelo impacto exponencial, nao pelo mais facil."
```

### Step 3: Sort by Impact Criteria

Order by:
1. **Impact if it remains invisible** (CRITICO first)
2. **Ease of resolution** (quick wins among same impact level)
3. **Dependencies** (what unblocks other findings)

### Step 4: Extract Top 5

Select the 5 highest-priority items. Ensure representation across axes when impact levels are equal.

```yaml
top_5:
  - rank: 1
    id: ""
    axis: "P | H | PC | D | EV"
    nome: ""
    impacto: "CRITICO"
    pergunta_chave: ""
  - rank: 2
    ...
```

### Step 5: Detect Meta-Patterns

Scan the full findings list for recurring themes across axes:

- Are multiple findings rooted in the same assumption?
- Is there a systemic bias (e.g., "tendency to assume unlimited resources")?
- Do evasion patterns correlate with blind spots?

```yaml
meta_patterns:
  - pattern: ""
    supporting_findings: ["P-001", "PC-002"]
  - pattern: ""
    supporting_findings: []
```

## Output

```yaml
prioritized_findings:
  top_5:
    - rank: 1
      id: ""
      axis: ""
      nome: ""
      impacto: ""
      pergunta_chave: ""
    # ... ranks 2-5
  meta_patterns:
    - pattern: ""
      supporting_findings: []
  full_ranked_list:
    - id: ""
      axis: ""
      nome: ""
      impacto: ""
      rank: 0
  total_findings:
    critico: 0
    alto: 0
    medio: 0
```

## Acceptance Criteria

- [ ] All findings consolidated into single ranked list [threshold: >= 1]
- [ ] Pareto-ao-Cubo checkpoint applied (not linear sorting) [threshold: >= 1]
- [ ] Top 5 items selected with cross-axis representation when possible [threshold: >= 5]
- [ ] Meta-patterns identified with supporting finding IDs [threshold: >= 1]
- [ ] Sort criteria documented (impact > ease > dependencies) [threshold: >= 3]

## Veto Conditions

None specific to this phase. Parent veto conditions apply.

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-implicit.md` | Parent orchestrator |
| `extract-implicit-analyze.md` | Previous phase (deep analysis) |
| `extract-implicit-synthesize.md` | Next phase (output assembly) |
