<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-deduplication
  task_name: Squad Fusion - Deduplication
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 45m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Analisar inventarios fonte
  - Detectar duplicatas e conflitos
  acceptance_criteria:
  - Every component from inventory appears in exactly one merge-plan category [threshold: >= 1]
  - No component is silently omitted from analysis [threshold: >= 1]
  - Duplicate detection uses both name and content similarity [threshold: >= 2]
  - All conflicts have at least 2 resolution options [threshold: >= 2]
  - QUALITY mode presents human checkpoint; YOLO mode auto-validates [threshold: >= 1]
  - Duplicatas sao resolvidas por semantica, nao so por nome [threshold: >= 1]
  - Toda exclusao tem provenance [threshold: >= 1]
  - O output pode ser consumido pela fase de escopo [threshold: score >= 0.8]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Squad Fusion - Deduplication

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-deduplication` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |
| **Merges** | `squad-fusion-deduplication` + `squad-fusion-analysis` |

## Metadata

```yaml
id: squad-fusion-deduplication
name: "Squad Fusion Deduplication"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Analisa inventarios fonte, detecta duplicatas semanticas, conflitos e gaps. Produz merge plan categorizado e define registros canonicos com provenance."
```

## Purpose

Analisar os inventarios dos squads fonte para detectar duplicatas, conflitos e gaps. Produzir um merge plan categorizado (keep/merge/discard) com golden records e rationale documentado para cada decisao.

## Workflow / Steps

### Step 1: Analisar inventarios fonte

Detectar duplicatas, conflitos e gaps entre os componentes inventariados.

#### 1.1: Detect Duplicates

```yaml
detect_duplicates:
  method: "multi-criteria"
  criteria:
    - name_similarity: 0.8   # Threshold for filename match
    - content_similarity: 0.7 # Threshold for content overlap
    - purpose_match: true     # Semantic purpose alignment
  output: "duplicates.yaml"
  per_duplicate:
    - component_a: "{path}"
    - component_b: "{path}"
    - similarity_score: N
    - recommendation: "keep_a | keep_b | merge | keep_both"
```

#### 1.2: Detect Conflicts

```yaml
detect_conflicts:
  types:
    - name_collision: "Same filename in different squads"
    - config_conflict: "Different values for same key in config.yaml"
    - dependency_conflict: "Incompatible dependencies between squads"
  output: "conflicts.yaml"
  per_conflict:
    - type: "{conflict_type}"
    - description: "{human-readable description}"
    - sources: ["{squad-a}", "{squad-b}"]
    - resolution_options: ["option_1", "option_2", ...]
```

#### 1.3: Identify Gaps

```yaml
identify_gaps:
  check:
    - "Missing orchestrator agent in combined set"
    - "Missing config.yaml fields for target"
    - "Missing README.md content"
    - "Orphan dependencies (referenced but not present)"
  output: "gaps.yaml"
  per_gap:
    - type: "{gap_type}"
    - severity: "blocking | recommended"
    - remediation: "{suggested fix}"
```

### Step 2: Detectar duplicatas e definir golden records

Resolver entidades duplicadas e decidir registros canonicos.

#### 2.1: Detectar colisoes reais

- Comparar nomes, funcao, outputs e dependencias dos assets.
- Diferenciar duplicata real de variante complementar.

#### 2.2: Definir golden records e merge plan

- Escolher versao canonica por qualidade, completude e aderencia ao target.
- Produzir listas `assets_to_keep` e `assets_to_exclude`.
- Gerar merge plan categorizado (keep/merge/discard) com rationale.

```yaml
generate_merge_plan:
  output: "merge-plan.yaml"
  contents:
    components_to_keep:
      - "{path}" # Unique components, no conflicts
    components_to_merge:
      - sources: ["{path_a}", "{path_b}"]
        strategy: "content_merge | best_of"
    components_to_discard:
      - path: "{path}"
        reason: "{why discarded}"
    conflicts_requiring_decision:
      - "{conflict reference}" # Only in QUALITY mode
```

### Step 3: Checkpoint

```yaml
checkpoint:
  type: "{mode == 'quality' ? 'human' : 'automatic'}"
  display: |
    ANALYSIS REPORT

    Duplicates Found: {duplicates.count}
    Conflicts Found: {conflicts.count}
    Gaps Identified: {gaps.count}

    DUPLICATES:
    {for dup in duplicates}
      - {dup.name}: {dup.sources}
        Similarity: {dup.similarity}%
        Recommendation: {dup.recommendation}
    {/for}

    CONFLICTS:
    {for conflict in conflicts}
      - {conflict.type}: {conflict.description}
        Resolution options: {conflict.options}
    {/for}

  validate:
    - "Merge plan generated"
    - "All duplicates categorized"
    - "All conflicts have resolution options"
```

## Output

```yaml
# Analysis artifacts
analysis:
  duplicates: "duplicates.yaml"   # All detected duplicate pairs with similarity scores
  conflicts: "conflicts.yaml"     # All detected conflicts with resolution options
  gaps: "gaps.yaml"               # All identified gaps with remediation suggestions
  merge_plan: "merge-plan.yaml"   # Categorized component list (keep/merge/discard)

# Deduplication artifacts
deduplication:
  duplicates_found: []
  duplicates_resolved: []
  assets_to_keep: []
  assets_to_exclude: []
```

## Acceptance Criteria

- [ ] Every component from inventory appears in exactly one merge-plan category [threshold: >= 1]
- [ ] No component is silently omitted from analysis [threshold: >= 1]
- [ ] Duplicate detection uses both name and content similarity [threshold: >= 2]
- [ ] All conflicts have at least 2 resolution options [threshold: >= 2]
- [ ] QUALITY mode presents human checkpoint; YOLO mode auto-validates [threshold: >= 1]
- [ ] Duplicatas sao resolvidas por semantica, nao so por nome [threshold: >= 1]
- [ ] Toda exclusao tem provenance [threshold: >= 1]
- [ ] O output pode ser consumido pela fase de escopo [threshold: score >= 0.8]

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-SFU-002 | Analysis reports not generated before proceeding to merge | BLOCK. Execute analysis first. |

## Related Documents

- `squad-fusion.md` -- Parent stub task
- `squad-fusion-discovery.md` -- Previous phase (Phase 2)
- `squad-fusion-scope.md` -- Next phase (Phase 4)

_Task Version: 2.0.0 -- Merged from squad-fusion-deduplication + squad-fusion-analysis_
