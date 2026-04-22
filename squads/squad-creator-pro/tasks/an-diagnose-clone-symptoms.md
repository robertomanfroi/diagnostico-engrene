<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-diagnose-clone-symptoms
  task_name: Diagnose Clone -- Symptoms + Root Cause
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Identify Symptoms
  - Map to Root Cause (BINARY -- Use Table Only)
  acceptance_criteria:
  - All reported symptoms documented
  - Each symptom mapped to root cause via lookup table
  - No causes invented outside the table
  - Unmapped symptoms flagged separately
  - All symptoms mapped to causes via table
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: Diagnose Clone -- Symptoms + Root Cause

**Task ID:** an-diagnose-clone-symptoms
**Parent Task:** `an-diagnose-clone.md`
**Purpose:** Identify clone symptoms and map to root causes using deterministic lookup table
**Execution Type:** Agent
**Model:** Sonnet
**Haiku Eligible:** NO
**Load:** `data/an-clone-anti-patterns.yaml`

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Diagnose Clone -- Symptoms + Root Cause |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | User description of clone problems |
| **output** | Symptoms list + root causes from lookup table |
| **action_items** | 2 steps |
| **acceptance_criteria** | All symptoms mapped to causes via table, no inference |

---

## Workflow

### Step 1: Identify Symptoms

Ask the user: "O que esta errado com o clone?"

Common symptoms:

- "Responde generico" -> probably missing Framework
- "Nao parece a pessoa" -> bronze sources or no Voice DNA
- "Se perde em conversas longas" -> monolithic prompt, needs stages
- "Quebra facil" -> no veto conditions, weak immune system
- "Inventa coisas" -> no Swipe File, no limits
- "Muito robotico" -> no productive contradictions, no storytelling

### Step 2: Map to Root Cause (BINARY -- Use Table Only)

```yaml
checkpoint_root_cause:
  rule: "SE sintoma esta na tabela abaixo -> usar causa da tabela"
  NO_INFERENCE: "Nao inventar causas fora da tabela"
  validation: "Causa DEVE estar na coluna 'Causa Raiz Provavel'"
```

Use `an-clone-anti-patterns.yaml` to diagnose:

| Sintoma | Causa Raiz Provavel | Anti-pattern |
|---------|---------------------|-------------|
| Generico | Falta Framework | So Playbook, sem SE/ENTAO |
| Nao parece pessoa | Fontes bronze | Volume sem curadoria |
| Se perde | Prompt monolitico | Sem estagios |
| Quebra facil | Sem immune system | Sem veto conditions |
| Inventa | Sem Swipe File | Sem exemplos reais |
| Robotico | Sem paradoxos | Contradictions resolvidas |

---

## Output Contract

```yaml
symptom_diagnosis:
  clone: "{name}"
  symptoms:
    - symptom: "{description}"
      root_cause: "{from lookup table}"
      anti_pattern: "{from lookup table}"
  unmapped_symptoms: []  # symptoms not in lookup table
```

---

## Completion Criteria

- [ ] All reported symptoms documented
- [ ] Each symptom mapped to root cause via lookup table
- [ ] No causes invented outside the table
- [ ] Unmapped symptoms flagged separately

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `an-diagnose-clone-verify-trinity.md` |
| **Trigger** | Symptoms mapped |
| **Artifact** | `symptom_diagnosis` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-diagnose-clone.md_

## Acceptance Criteria

- [ ] All symptoms mapped to causes via table
- [ ] no inference
