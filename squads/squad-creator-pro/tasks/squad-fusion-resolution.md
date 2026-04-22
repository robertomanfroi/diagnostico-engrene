<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-resolution
  task_name: Squad Fusion -- Resolution
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Resolve Duplicates
  - Resolve Conflicts
  - Fill Gaps
  - Checkpoint
  acceptance_criteria:
  - Zero unresolved duplicates remain
  - Zero unresolved conflicts remain
  - Zero unfilled blocking gaps remain
  - Every resolution has documented rationale
  - Updated merge plan reflects all decisions
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


# Task: Squad Fusion -- Resolution

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-resolution` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `hybrid` (Agent in YOLO, Human in QUALITY) |

## Metadata

```yaml
id: squad-fusion-resolution
name: "Squad Fusion Resolution"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Resolve duplicatas, conflitos e gaps. Em YOLO aplica estrategias deterministicas; em QUALITY apresenta cada decisao para aprovacao humana."
```

## Purpose

Resolver cada duplicata, conflito e gap identificado na fase de Analysis. Em YOLO, aplicar estrategias de resolucao automaticamente. Em QUALITY, apresentar cada decisao ao humano com rationale documentado.

## Workflow / Steps

### Step 1: Resolve Duplicates

```yaml
resolve_duplicates:
  strategy:
    yolo:
      - prefer_newer: true
      - prefer_longer: true   # More content = more complete
      - merge_if_complementary: true
    quality:
      - present_options_to_human
      - await_decision
      - document_rationale
```

**Duplicate Resolution Matrix:**

| Scenario | YOLO Strategy | QUALITY Strategy |
|----------|---------------|------------------|
| Same name, different content | Keep longer one | Human chooses |
| Same purpose, different approach | Merge best parts | Human reviews merge |
| Complementary specialties | Keep both, rename | Human confirms |

### Step 2: Resolve Conflicts

```yaml
resolve_conflicts:
  for_each: "{conflicts}"
  strategies:
    name_collision:
      - rename_with_prefix: "{source_squad}-{original_name}"
      - keep_one_discard_other
      - merge_into_new
    config_conflict:
      - deep_merge: "Combine both configs"
      - prefer_source: "Use specific source's config"
      - manual_edit: "Human edits merged config"
    dependency_conflict:
      - update_to_latest
      - keep_both_with_alias
      - remove_conflicting
```

**Config Conflict Resolution:**

| Conflict Type | Resolution |
|---------------|------------|
| Different versions | Use higher version |
| Different descriptions | Concatenate |
| Different settings | Deep merge, prefer source A for conflicts |

**Dependency Conflict Resolution:**

| Conflict Type | Resolution |
|---------------|------------|
| Same dependency, different versions | Use latest |
| Circular dependencies | Break cycle, warn user |
| Missing dependencies | Add to target, warn user |

### Step 3: Fill Gaps

```yaml
fill_gaps:
  actions:
    missing_orchestrator:
      - create_from_template
      - promote_existing_agent
    missing_config:
      - generate_from_sources
    missing_readme:
      - generate_from_template
```

### Step 4: Checkpoint

```yaml
checkpoint:
  type: "{mode == 'quality' ? 'human' : 'automatic'}"
  validate:
    - "All duplicates resolved"
    - "All conflicts resolved"
    - "All gaps filled"
    - "Resolution log complete"
```

## Output

```yaml
# resolution-log.yaml
resolved_duplicates:
  - pair: ["{path_a}", "{path_b}"]
    decision: "keep_a | keep_b | merge | keep_both"
    rationale: "{why}"

resolved_conflicts:
  - conflict_id: "{id}"
    resolution: "{chosen strategy}"
    rationale: "{why}"

filled_gaps:
  - gap_type: "{type}"
    action_taken: "{what was done}"

updated_merge_plan:
  # Final merge plan with all decisions applied
  components_to_keep: [...]
  components_to_merge: [...]
  components_to_discard: [...]
```

## Acceptance Criteria

- [ ] Zero unresolved duplicates remain
- [ ] Zero unresolved conflicts remain
- [ ] Zero unfilled blocking gaps remain
- [ ] Every resolution has documented rationale
- [ ] Updated merge plan reflects all decisions
- [ ] QUALITY mode: every decision approved by human

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-SFU-002 | Proceeding to merge without completing resolution | BLOCK. All items must be resolved. |

## Related Documents

- `squad-fusion.md` -- Parent stub task
- `squad-fusion-deduplication.md` -- Previous phase (Dedup + Analysis)
- `squad-fusion-execution.md` -- Next phase (Phase 4)
