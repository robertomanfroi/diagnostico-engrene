<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-diagnose-clone-prescribe
  task_name: Diagnose Clone -- Prescribe + Report
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
  - Prescribe Treatment (BINARY -- Use Table)
  - Generate Report
  acceptance_criteria:
  - Treatment prescribed for each root cause using lookup table
  - Priorities assigned from table (URGENTE > ALTA > MEDIA)
  - All report fields populated (non-empty)
  - Prognosis with concrete percentage improvement estimate
  - Treatments from lookup table only
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


# Task: Diagnose Clone -- Prescribe + Report

**Task ID:** an-diagnose-clone-prescribe
**Parent Task:** `an-diagnose-clone.md`
**Purpose:** Prescribe treatment from lookup table and generate diagnosis report
**Execution Type:** Agent
**Model:** Sonnet
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Diagnose Clone -- Prescribe + Report |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `symptom_diagnosis` + `trinity_verification` from prior sub-tasks |
| **output** | Treatment plan + `diagnosis_report` YAML |
| **action_items** | 2 steps |
| **acceptance_criteria** | Treatments from lookup table only, report complete |

---

## Workflow

### Step 1: Prescribe Treatment (BINARY -- Use Table)

```yaml
checkpoint_tratamento:
  rule: "SE causa esta na tabela abaixo -> usar tratamento da tabela"
  NO_INFERENCE: "Nao inventar tratamentos fora da tabela"
  priority_rule: "Usar prioridade EXATA da tabela (URGENTE > ALTA > MEDIA)"
```

| Causa | Tratamento | Prioridade |
|-------|------------|------------|
| Falta Framework | Extrair regras SE/ENTAO de entrevistas | URGENTE |
| Fontes bronze | Reclassificar, buscar ouro | URGENTE |
| Sem estagios | Mapear contextos, criar stages | ALTA |
| Sem Swipe | Coletar exemplos reais | ALTA |
| Sem immune | Definir veto conditions | MEDIA |
| Sem paradoxos | Mapear contradictions produtivas | MEDIA |

### Step 2: Generate Report

```yaml
checkpoint_report_complete:
  rule: "SE todos campos do template estao preenchidos (non-empty) -> COMPLETO"
  required_fields:
    - "clone: non-empty"
    - "symptoms: 1+ items"
    - "root_causes: 1+ items com cause + evidence + severity"
    - "trinity_status: playbook + framework + swipe_file preenchidos"
    - "source_quality: ouro|mixed|bronze"
    - "treatment: 1+ items com action + priority + effort"
    - "prognosis: non-empty"
```

---

## Output Contract

```yaml
diagnosis_report:
  clone: "{name}"
  symptoms: [{list}]
  root_causes:
    - cause: "{cause}"
      evidence: "{evidence}"
      severity: "critico|alto|medio"
  trinity_status:
    playbook: "presente|ausente|parcial"
    framework: "presente|ausente|parcial"
    swipe_file: "presente|ausente|parcial"
  source_quality: "ouro|mixed|bronze"
  fidelity_score: {0-100}
  treatment:
    - action: "{what to do}"
      priority: "urgente|alta|media"
      effort: "{estimate}"
  prognosis: "Com essas acoes, fidelidade deve subir de {X}% para {Y}%"
```

---

## Completion Criteria

- [ ] Treatment prescribed for each root cause using lookup table
- [ ] Priorities assigned from table (URGENTE > ALTA > MEDIA)
- [ ] All report fields populated (non-empty)
- [ ] Prognosis with concrete percentage improvement estimate

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of an-diagnose-clone.md_

## Acceptance Criteria

- [ ] Treatments from lookup table only
- [ ] report complete
