<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: find-0-8-classify
  task_name: find-0-8 -- Classify
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
  - Collect Activities
  - Apply Checklist Lendario (Decision Flow)
  acceptance_criteria:
  - E sua maior paixao em acao?
  - Transforma o "impossivel" em realidade?
  - Ninguem mais consegue fazer igual?
  - Gera resultados exponenciais?
  - Pode ser multiplicado pela IA (nao substituido)?
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


# Task: find-0-8 -- Classify

**Task ID:** find-0-8-classify
**Parent Task:** `find-0-8.md`
**Purpose:** Apply 4 zones and Checklist Lendario decision flow to classify activities
**Execution Type:** Agent
**Model:** `Sonnet`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | find-0-8 -- Classify |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | List of activities/knowledge areas |
| **output** | Classified activities in 4 zones with justifications |
| **action_items** | 2 steps |
| **acceptance_criteria** | All activities classified, decision flow applied in order |

---

## The 4 Zones

### Zona de Genialidade (0,8%) -- ~51% dos resultados

Validation:

- [ ] E sua maior paixao em acao?
- [ ] Transforma o "impossivel" em realidade?
- [ ] Ninguem mais consegue fazer igual?
- [ ] Gera resultados exponenciais?
- [ ] Pode ser multiplicado pela IA (nao substituido)?

### Zona de Excelencia (4%) -- ~64% dos resultados

Validation:

- [ ] Requer sua expertise unica?
- [ ] Gera resultados consistentes?
- [ ] Pouquissimas pessoas fazem tao bem?
- [ ] Tem potencial de escala?

### Zona de Impacto (20%) -- ~80% dos resultados

Validation:

- [ ] E estrategicamente importante?
- [ ] Requer conhecimento especifico?
- [ ] Gera resultados significativos?
- [ ] Pode ser sistematizado?

### Zona de Merda (80%) -- ~20% dos resultados ou menos

Validation:

- [ ] E repetitivo ou burocratico?
- [ ] Pode ser feito pela IA?
- [ ] Qualquer pessoa faria com treino basico?
- [ ] Consome energia sem gerar impacto real?

---

## Workflow

### Step 1: Collect Activities

Gather the list of activities/knowledge areas to classify. These may come from:

- User input
- Squad agent analysis
- Workflow audit results
- Expert interview data

### Step 2: Apply Checklist Lendario (Decision Flow)

Apply questions IN ORDER for each activity:

#### 1. Teste de Impacto

> "Essa atividade gera resultados lendarios?"

- **NAO** -> E 80% (Zona de Merda)
- **SIM** -> Continue

#### 2. Teste de Singularidade

> "So eu consigo fazer isso com excelencia?"

- **NAO** -> Continue to 3
- **SIM** -> Continue to 4

#### 3. Teste de Valor

> "Isso gera resultados importantes mesmo nao sendo unico?"

- **NAO** -> E 80% (Zona de Merda)
- **SIM** -> E 20% (Zona de Impacto)

#### 4. Teste de Genialidade

> "Isso me coloca em estado de flow e gera resultados lendarios?"

- **NAO** -> E 4% (Zona de Excelencia)
- **SIM** -> E 0,8% (Zona de Genialidade)

---

## Output Contract

```yaml
classification:
  activities:
    - name: "{activity}"
      zone: "0.8%|4%|20%|80%"
      test_results:
        impacto: "SIM|NAO"
        singularidade: "SIM|NAO|N/A"
        valor: "SIM|NAO|N/A"
        genialidade: "SIM|NAO|N/A"
      justification: "{why this zone}"
  summary:
    genius_08: [{activities}]
    excellence_4: [{activities}]
    impact_20: [{activities}]
    waste_80: [{activities}]
```

---

## Completion Criteria

- [ ] All activities passed through Checklist Lendario in order
- [ ] Each activity classified in exactly one zone
- [ ] Justification provided for each classification
- [ ] Summary by zone generated

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `find-0-8-recommend.md` |
| **Trigger** | Classification complete |
| **Artifact** | `classification` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of find-0-8.md_

## Acceptance Criteria

- [ ] All activities classified
- [ ] decision flow applied in order
