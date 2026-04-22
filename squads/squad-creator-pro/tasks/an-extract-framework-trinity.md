---
task-id: an-extract-framework-trinity
name: "Extract Playbook, Framework & Swipe File"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Deep semantic extraction of methodology, decision rules, and examples."
haiku_eligible: false
estimated-time: 30 min
complexity: medium

inputs:
  required:
    - source: "Source material"
    - source_quality: "OURO or BRONZE from Phase 1"
    - gap_analysis: "GAP analysis from Phase 1"

outputs:
  primary:
    - playbook: "Step-by-step methodology"
    - framework: "SE/ENTAO decision rules"
    - swipe_file: "Real examples and cases"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-framework-trinity
  task_name: Extract Playbook, Framework & Swipe File
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - '{''source'': ''Source material''}'
  - '{''source_quality'': ''OURO or BRONZE from Phase 1''}'
  - '{''gap_analysis'': ''GAP analysis from Phase 1''}'
  output:
  - '{''playbook'': ''Step-by-step methodology''}'
  - '{''framework'': ''SE/ENTAO decision rules''}'
  - '{''swipe_file'': ''Real examples and cases''}'
  action_items:
  - Extract Playbook
  - Extract Framework
  - Extract Swipe File
  acceptance_criteria:
  - Playbook has clear sequential steps
  - Framework has SE/ENTAO rules (not just theory)
  - Swipe File has REAL examples (not invented)
  - The three complement each other (Playbook=WHAT, Framework=WHEN, Swipe=HOW)
  - Framework vs Playbook checkpoint passed
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


# Task: Extract Playbook, Framework & Swipe File

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-extract-framework-trinity` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `an-extract-framework` (orchestrator stub)
- **Sequence:** Phase 2 of 3
- **Previous Task:** `an-extract-framework-analyze`
- **Next Task:** `an-extract-framework-integrate`

## Purpose

Extract the complete Trinity: Playbook (O QUE fazer), Framework (QUANDO/POR QUE), and Swipe File (COMO -- real examples).

## Workflow / Steps

### Step 1: Extract Playbook

The Playbook is the RECIPE -- step-by-step methodology.

Search in source:
- "Como ele faz X?" -- sequence of steps
- "Qual o processo dele?" -- workflow
- "O que faz primeiro, segundo, terceiro?" -- order

```yaml
playbook:
  name: "{nome da metodologia}"
  steps:
    - step: 1
      action: "{o que fazer}"
      details: "{como fazer}"
    - step: 2
      action: "{proximo passo}"
```

### Step 2: Extract Framework

The Framework is the FORM -- SE/ENTAO decision rules.

Search in source:
- "Quando ele ve X, o que faz?" -- conditional rule
- "Como decide entre A e B?" -- criteria
- "O que NUNCA faria?" -- veto condition

```yaml
framework:
  rules:
    - condition: "SE {situacao}"
      action: "ENTAO {decisao}"
      rationale: "{por que}"
  veto:
    - condition: "SE {situacao}"
      action: "NUNCA {acao proibida}"
```

**Checkpoints:**

```yaml
checkpoint_clareza_radical:
  question: "Framework extraido tem regras claras SE/ENTAO?"
  if_claras: "Framework valido"
  if_vagas: "Refazer extracao buscando condicoes explicitas"

checkpoint_profundidade:
  question: "Extrai FRAMEWORK (SE/ENTAO) ou so PLAYBOOK (passos)?"
  if_framework: "Regras de decisao documentadas — valido"
  if_playbook: "Continuar extracao ate achar regras condicionais"
```

### Step 3: Extract Swipe File

The Swipe File is EXAMPLES -- proof that it works.

Search in source:
- Real cases with numbers
- Specific examples cited
- Analogies and metaphors used
- Stories told repeatedly

```yaml
swipe_file:
  cases:
    - title: "{caso}"
      context: "{situacao}"
      result: "{resultado}"
      lesson: "{licao}"
  analogies:
    - concept: "{conceito}"
      analogy: "{analogia usada}"
```

**Checkpoint:**

```yaml
checkpoint_swipe_autenticidade:
  question: "Exemplos sao REAIS do expert ou GENERICOS do campo?"
  if_reais: "Swipe File valido"
  if_genericos: "Marcar como [GENERIC] e buscar casos reais"
```

## Output

```yaml
playbook: { name, steps }
framework: { rules, veto }
swipe_file: { cases, analogies }
```

## Acceptance Criteria

- [ ] Playbook has clear sequential steps
- [ ] Framework has SE/ENTAO rules (not just theory)
- [ ] Swipe File has REAL examples (not invented)
- [ ] The three complement each other (Playbook=WHAT, Framework=WHEN, Swipe=HOW)
- [ ] Framework vs Playbook checkpoint passed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-extract-framework.md` | Parent orchestrator |
| `an-extract-framework-analyze.md` | Previous phase |
| `an-extract-framework-integrate.md` | Next phase |
