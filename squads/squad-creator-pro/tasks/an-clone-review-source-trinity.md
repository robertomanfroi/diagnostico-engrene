<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-clone-review-source-trinity
  task_name: Clone Review -- Source Quality + Trinity
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Source Quality Review
  - Trinity Verification (Binary Checkpoints)
  acceptance_criteria:
  - All sources evaluated with 5 binary checkpoints each
  - Curadoria score calculated (excelente/aceitavel/critico)
  - Playbook scored with 5 checkpoints
  - Framework scored with 5 checkpoints
  - Swipe File scored with 5 checkpoints
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


# Task: Clone Review -- Source Quality + Trinity

**Task ID:** an-clone-review-source-trinity
**Parent Task:** `an-clone-review.md`
**Purpose:** Evaluate source quality with binary checkpoints and verify Trinity (Playbook, Framework, Swipe File)
**Execution Type:** Hybrid (Worker script 90% + Agent interpretation 10%)
**Model:** `Haiku`
**Haiku Eligible:** YES

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Clone Review -- Source Quality + Trinity |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | Clone file path + preflight YAML from worker script |
| **output** | Source quality scores + Trinity scores |
| **action_items** | 2 steps |
| **acceptance_criteria** | All checkpoints scored binary, totals calculated |

---

## Prerequisite

```
READ /tmp/preflight-clone-review.yaml first. Use ONLY these numbers.
Do NOT count sources manually. Do NOT grep for checkpoints yourself.
```

---

## Workflow

### Step 1: Source Quality Review

**Where to look:** `sources/`, `metadata.yaml`, reference files

**Checkpoints per source:**

| # | Checkpoint | Passes if... |
|---|------------|-------------|
| 1 | Source file exists | File exists in sources/ |
| 2 | Source has type | Field `type:` defined |
| 3 | Source classified | Field `tier:` = ouro or bronze |
| 4 | Source has content | File has >100 useful lines |
| 5 | Source is primary | Referenced in agent file |

**Calculation:**

```python
total_sources = count(sources/)
ouro_sources = count(tier == "ouro")
ouro_percentage = (ouro_sources / total_sources) * 100

curadoria_score:
  if ouro_percentage >= 80: "excelente"
  elif ouro_percentage >= 60: "aceitavel"
  else: "critico"
```

### Step 2: Trinity Verification (Binary Checkpoints)

**For each leg of the trinity, verify 5 checkpoints:**

#### Playbook (5 checkpoints)

| # | Checkpoint | What to look for | Passes if... |
|---|------------|------------------|-------------|
| 1 | Section exists | `playbook:` or `workflow:` | Section exists in file |
| 2 | Has steps | `steps:` or numbered list | 3+ steps defined |
| 3 | Steps are sequential | Logical order | Steps have numbers or clear sequence |
| 4 | Steps are actionable | Action verbs | Each step starts with verb |
| 5 | Has output definition | `output:` per step | At least 1 step has output defined |

**Score Playbook = count(passed) -> 0-5**

#### Framework (5 checkpoints)

| # | Checkpoint | What to look for | Passes if... |
|---|------------|------------------|-------------|
| 1 | Section exists | `framework:` or `heuristics:` | Section exists |
| 2 | Has rules | `rules:` or `SE/ENTAO` | 3+ rules defined |
| 3 | Rules are conditional | `if:`, `when:`, `SE:` | Rules have conditions |
| 4 | Rules have actions | `then:`, `ENTAO:`, `action:` | Rules have consequences |
| 5 | Has decision tree | Nested structure | Rules have branching |

**Score Framework = count(passed) -> 0-5**

#### Swipe File (5 checkpoints)

| # | Checkpoint | What to look for | Passes if... |
|---|------------|------------------|-------------|
| 1 | Section exists | `examples:` or `swipe:` | Section exists |
| 2 | Has examples | List of examples | 3+ examples |
| 3 | Examples are real | `[SOURCE:]` tags | Examples have citation |
| 4 | Examples show input/output | Before/after pairs | At least 2 pairs |
| 5 | Examples are diverse | Different types | 2+ example types |

**Score Swipe File = count(passed) -> 0-5**

#### Trinity Total Score

```python
trinity_total = playbook_score + framework_score + swipe_score  # 0-15
trinity_percentage = (trinity_total / 15) * 100

trinity_verdict:
  if trinity_percentage >= 80: "SOLID"
  elif trinity_percentage >= 60: "NEEDS_WORK"
  else: "REBUILD"
```

---

## Output Contract

```yaml
source_trinity_scores:
  source_quality:
    total_sources: {n}
    ouro_count: {n}
    bronze_count: {n}
    ouro_percentage: "{%}"
    curadoria_score: "excelente|aceitavel|critico"
    sources_checked:
      - file: "{name}"
        tier: "ouro|bronze"
        checkpoints_passed: [1,2,3,4,5]
  trinity:
    playbook:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    framework:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    swipe_file:
      checkpoints_passed: []
      checkpoints_failed: []
      score: {0-5}
      gaps: []
    total_score: {0-15}
    max_score: 15
    percentage: "{%}"
    verdict: "SOLID|NEEDS_WORK|REBUILD"
```

---

## Completion Criteria

- [ ] All sources evaluated with 5 binary checkpoints each
- [ ] Curadoria score calculated (excelente/aceitavel/critico)
- [ ] Playbook scored with 5 checkpoints
- [ ] Framework scored with 5 checkpoints
- [ ] Swipe File scored with 5 checkpoints
- [ ] Trinity total and verdict calculated

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `an-clone-review-stages-fidelity.md` |
| **Trigger** | Source + Trinity scores complete |
| **Artifact** | `source_trinity_scores` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-clone-review.md_

## Acceptance Criteria

- [ ] All checkpoints scored binary
- [ ] totals calculated
