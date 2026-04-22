---
task-id: collect-sources-classify
name: "Classify Sources by Tier"
version: 1.0.0
execution_type: Hybrid
model: Sonnet
model_rationale: "Source classification (ouro vs bronze) requires semantic judgment for quality assessment. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - discovered_sources: "Lista bruta de fontes descobertas (output de collect-sources-discover)"

outputs:
  primary:
    - sources_by_tier: "Fontes classificadas por Tier 1/2/3 com contagens e volumes"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources-classify
  task_name: Classify Sources by Tier
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''discovered_sources'': ''Lista bruta de fontes descobertas (output de collect-sources-discover)''}'
  output:
  - '{''sources_by_tier'': ''Fontes classificadas por Tier 1/2/3 com contagens e volumes''}'
  action_items:
  - Apply Tier Classification System
  - Organize by Tier
  - Calculate Tier Distribution
  acceptance_criteria:
  - Every discovered source assigned exactly one tier (0, 1, 2, or 3) [threshold: 100% sources classified]
  - Classification follows DNA Mental OURO/BRONZE methodology [threshold: >= 1 methodology applied]
  - Estimated content volume provided for all Tier 0 and Tier 1 sources [threshold: 100% Tier 0+1 with volume]
  - Tier distribution summary calculated with gold/bronze ratio [threshold: >= 1 summary]
  - Gold ratio (Tier 0+1 / total) computed for downstream quality decisions [threshold: >= 50%]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
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


# Task: Classify Sources by Tier

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `collect-sources-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `collect-sources` (orchestrator stub)
- **Sequence:** Phase 2 of 5
- **Previous Task:** `collect-sources-discover`
- **Next Task:** `collect-sources-validate`
- **Specialist:** `@oalanicolas` (DNA Mental source curation: OURO vs BRONZE)

## Purpose

Classify all discovered sources into the 3-tier system based on proximity to the expert. Tier 1 (primary/OURO) sources come directly from the expert. Tier 2 (secondary) sources are about the expert. Tier 3 (tertiary/BRONZE) sources are aggregated or summarized content. This classification drives quality decisions downstream.

## Prerequisites

- `collect-sources-discover` task completed successfully
- `discovered_sources` output available with cataloged sources

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `discovered_sources` | Yes | Raw source list from discovery phase |

## Workflow / Steps

### Step 1: Apply Tier Classification System

Classify each source using these criteria:

| Tier | Tipo | Confianca | Exemplos |
|------|------|-----------|----------|
| **Tier 0** | User-provided (do expert, fornecido pelo usuario) | MAXIMA | PDFs proprios, notas, gravacoes |
| **Tier 1** | Primario (do expert) | ALTA | Livros proprios, entrevistas diretas, cursos |
| **Tier 2** | Secundario (sobre expert) | MEDIA | Biografias, case studies, reviews |
| **Tier 3** | Terciario (agregado) | BAIXA | Wikipedia, resumos de terceiros, compilacoes |

**DNA Mental Classification Rules:**
- **OURO (Gold):** Direct from expert = Tier 0-1
- **BRONZE:** About expert = Tier 2-3
- Apply 40/20/40 rule: 40% curadoria, 20% prompt, 40% refinamento

### Step 2: Organize by Tier

For each source, assign tier and estimate content volume:

```yaml
sources_by_tier:
  tier_0_user_provided:
    count: 0
    items:
      - source: ""
        type: ""
        estimated_content: "X horas / Y paginas"

  tier_1_primary:
    count: 0
    items:
      - source: ""
        type: ""
        estimated_content: "X horas / Y paginas"

  tier_2_secondary:
    count: 0
    items:
      - source: ""
        type: ""

  tier_3_tertiary:
    count: 0
    items:
      - source: ""
        type: ""
```

### Step 3: Calculate Tier Distribution

Summarize the distribution:

```yaml
tier_summary:
  total_sources: 0
  tier_0_count: 0
  tier_1_count: 0
  tier_2_count: 0
  tier_3_count: 0
  gold_ratio: "0%"   # (tier_0 + tier_1) / total
  bronze_ratio: "0%"  # (tier_2 + tier_3) / total
```

Target: gold_ratio >= 50% for high-fidelity clone.

## Output

```yaml
sources_by_tier:
  tier_0_user_provided:
    count: 0
    items: []
  tier_1_primary:
    count: 0
    items: []
  tier_2_secondary:
    count: 0
    items: []
  tier_3_tertiary:
    count: 0
    items: []
tier_summary:
  total_sources: 0
  gold_ratio: "0%"
  bronze_ratio: "0%"
```

## Acceptance Criteria

- [ ] Every discovered source assigned exactly one tier (0, 1, 2, or 3) [threshold: 100% sources classified]
- [ ] Classification follows DNA Mental OURO/BRONZE methodology [threshold: >= 1 methodology applied]
- [ ] Estimated content volume provided for all Tier 0 and Tier 1 sources [threshold: 100% Tier 0+1 with volume]
- [ ] Tier distribution summary calculated with gold/bronze ratio [threshold: >= 1 summary]
- [ ] Gold ratio (Tier 0+1 / total) computed for downstream quality decisions [threshold: >= 50%]

## Veto Conditions

None specific to this phase. Parent veto conditions (VETO-CSR-001, VETO-CSR-002) apply from discovery.

## Related Documents

| Document | Relationship |
|----------|-------------|
| `collect-sources.md` | Parent orchestrator |
| `collect-sources-discover.md` | Previous phase (source discovery) |
| `collect-sources-validate.md` | Next phase (coverage validation) |
