<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: find-0-8-recommend
  task_name: find-0-8 -- Recommend
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
  - Generate Actions Per Zone
  - Generate Report
  acceptance_criteria:
  - Each zone has specific action recommendations
  - 0.8% activities have protection actions defined
  - 80% activities have eliminate/automate/delegate actions
  - Golden rules applied where relevant
  - Final report generated
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: find-0-8 -- Recommend

**Task ID:** find-0-8-recommend
**Parent Task:** `find-0-8.md`
**Purpose:** Generate action recommendations per zone and produce final output report
**Execution Type:** Agent
**Model:** `Sonnet`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | find-0-8 -- Recommend |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `classification` YAML from `find-0-8-classify.md` |
| **output** | Action plan + Pareto report |
| **action_items** | 2 steps |
| **acceptance_criteria** | Each zone has specific actions, 0.8% protected |

---

## Workflow

### Step 1: Generate Actions Per Zone

#### For 80% (Eliminate/Automate/Delegate)

**Killer questions:**

- "Se eu simplesmente parasse de fazer isso hoje, o que aconteceria de verdade?"
- "Alguem importante realmente sentiria falta disso?"
- "Trinity IA poderia fazer isso em segundos?"
- "Para quem isso seria um 4% ao inves de um 80%?"

| Acao | Como |
|------|------|
| **Eliminar** | Delete, cancele, diga nao |
| **Automatizar** | Use IA, crie templates, configure gatilhos |
| **Delegar** | Documente uma vez, treine uma vez, solte de vez |

#### For 20% (Systematize)

- Criar SOPs
- Documentar processos
- Treinar equipe

#### For 4% (Leverage)

- Manter alta qualidade
- Escalar com cuidado
- Nao diluir expertise

#### For 0,8% (Protect)

- Bloquear tempo sagrado
- Eliminar distracoes
- Multiplicar via IA (nao substituir)

**Golden Rules:**

- **Regra dos 2 Minutos:** < 2 min -> faca agora. > 2 min -> precisa de sistema.
- **Regra do "Hell Yeah!":** Se nao for um "HELL YEAH!" -> e um nao.
- **Regra do Bloco Sagrado:** Concentre a "merda" em blocos. Proteja o tempo de genialidade.

### Step 2: Generate Report

```yaml
pareto_report:
  context: "{what was analyzed}"
  date: "{date}"

  genius_08:
    - activity: "{name}"
      justification: "{why}"
      protection_action: "{how to protect}"

  excellence_4:
    - activity: "{name}"
      justification: "{why}"
      leverage_action: "{how to leverage}"

  impact_20:
    - activity: "{name}"
      justification: "{why}"
      systematize_action: "{how to systematize}"

  waste_80:
    - activity: "{name}"
      justification: "{why}"
      action: "eliminate|automate|delegate"
      how: "{specific action}"

  recommendations:
    eliminate: []
    automate: []
    delegate: []
    protect_08: []
```

---

## Completion Criteria

- [ ] Each zone has specific action recommendations
- [ ] 0.8% activities have protection actions defined
- [ ] 80% activities have eliminate/automate/delegate actions
- [ ] Golden rules applied where relevant
- [ ] Final report generated

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of find-0-8.md_

## Acceptance Criteria

- [ ] Each zone has specific actions
- [ ] 0.8% protected
