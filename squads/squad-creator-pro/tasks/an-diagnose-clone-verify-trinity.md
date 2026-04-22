<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-diagnose-clone-verify-trinity
  task_name: Diagnose Clone -- Verify Trinity
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
  - Trinity Check
  - Source Quality Check
  - Fidelity Score (CALCULATE -- Do Not Estimate)
  acceptance_criteria:
  - Trinity checked with binary rules (no interpretation)
  - Source quality assessed (ouro/mixed/bronze)
  - Fidelity score calculated mechanically
  - Threshold classification assigned
  - All checks binary
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


# Task: Diagnose Clone -- Verify Trinity

**Task ID:** an-diagnose-clone-verify-trinity
**Parent Task:** `an-diagnose-clone.md`
**Purpose:** Binary trinity check + source quality assessment + fidelity score calculation
**Execution Type:** Hybrid
**Model:** Sonnet
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Diagnose Clone -- Verify Trinity |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Hybrid |
| **input** | Clone file path |
| **output** | Trinity status + source quality + fidelity score |
| **action_items** | 3 steps |
| **acceptance_criteria** | All checks binary, fidelity calculated mechanically |

---

## Trinity Assessment Rules (BINARY -- No Interpretation)

```yaml
trinity_rules:
  playbook:
    PRESENTE: "SE arquivo tem section 'Step' ou 'Workflow' com 3+ steps documentados"
    PARCIAL: "SE tem 1-2 steps OU steps sem detalhes"
    AUSENTE: "SE nao tem section de workflow"
    check_method: "grep -c 'Step|Workflow|###' no arquivo"

  framework:
    PRESENTE: "SE arquivo tem 3+ heuristicas com formato 'SE X -> ENTAO Y' ou 'IF X THEN Y'"
    PARCIAL: "SE tem 1-2 heuristicas OU heuristicas sem formato SE/ENTAO"
    AUSENTE: "SE nao tem heuristicas documentadas"
    check_method: "grep -c 'SE.*ENTAO|IF.*THEN|rule:' no arquivo"

  swipe_file:
    PRESENTE: "SE arquivo tem section 'output_examples' com 5+ exemplos"
    PARCIAL: "SE tem 1-4 exemplos"
    AUSENTE: "SE tem 0 exemplos"
    check_method: "Contar entries em output_examples section"
```

---

## Workflow

### Step 1: Trinity Check

#### Playbook Check

```bash
grep -c 'Step\|Workflow\|###' {clone_file}
# SE >= 3 -> PRESENTE | SE 1-2 -> PARCIAL | SE 0 -> AUSENTE
```

#### Framework Check

```bash
grep -c 'SE.*ENTAO\|IF.*THEN\|rule:\|heuristic' {clone_file}
# SE >= 3 -> PRESENTE | SE 1-2 -> PARCIAL | SE 0 -> AUSENTE
```

#### Swipe File Check

```bash
# Count output examples in examples section
# SE >= 5 -> PRESENTE | SE 1-4 -> PARCIAL | SE 0 -> AUSENTE
```

### Step 2: Source Quality Check

```yaml
source_quality_rules:
  OURO: "SE >70% das fontes sao ouro (canonical, entrevistas, livros)"
  MIXED: "SE 30-70% sao ouro"
  BRONZE: "SE <30% sao ouro"
```

### Step 3: Fidelity Score (CALCULATE -- Do Not Estimate)

```yaml
fidelity_formula:
  base_trinity:
    playbook: "PRESENTE=30, PARCIAL=15, AUSENTE=0"
    framework: "PRESENTE=30, PARCIAL=15, AUSENTE=0"
    swipe_file: "PRESENTE=20, PARCIAL=10, AUSENTE=0"
  bonuses:
    source_quality: "OURO=+10, MIXED=+5, BRONZE=0"
    immune_system: "SE tem 3+ veto conditions -> +5, SENAO 0"
    paradoxes: "SE tem section contradictions/paradoxes -> +5, SENAO 0"
  calculation: "SUM(base_trinity) + SUM(bonuses)"
  max_score: 100
  thresholds:
    critico: "<50%"
    review: "50-70%"
    bom: "70-85%"
    excelente: ">85%"
```

---

## Output Contract

```yaml
trinity_verification:
  trinity_status:
    playbook: "presente|ausente|parcial"
    framework: "presente|ausente|parcial"
    swipe_file: "presente|ausente|parcial"
  source_quality: "ouro|mixed|bronze"
  fidelity_score:
    playbook: {30|15|0}
    framework: {30|15|0}
    swipe_file: {20|10|0}
    source_bonus: {10|5|0}
    immune_bonus: {5|0}
    paradox_bonus: {5|0}
    TOTAL: {sum}
    threshold: "critico|review|bom|excelente"
```

---

## Completion Criteria

- [ ] Trinity checked with binary rules (no interpretation)
- [ ] Source quality assessed (ouro/mixed/bronze)
- [ ] Fidelity score calculated mechanically
- [ ] Threshold classification assigned

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `an-diagnose-clone-prescribe.md` |
| **Trigger** | Trinity verification complete |
| **Artifact** | `trinity_verification` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-diagnose-clone.md_

## Acceptance Criteria

- [ ] All checks binary
- [ ] fidelity calculated mechanically
