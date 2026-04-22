<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: ics-domain-mapping
  task_name: ICS Phase 2 — Domain Mapping
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
  - '.1: Identificar Dominio do Squad'
  - '.2: Definir Session Schema'
  acceptance_criteria:
  - ics-audit completo com eligible=true
  - config_extract disponivel com read_paths e write_paths
  - primary_entity identificada a partir do config_extract
  - session_schema definido com campos required e optional
  - Dominio mapeado e consistente com workspace_integration do config.yaml
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: ICS Phase 2 — Domain Mapping

**Task ID:** ics-domain-mapping
**Parent:** install-context-stack (stub)
**Purpose:** Identificar entidades do dominio do squad, mapear paths canonicos e definir session-context schema
**Orchestrator:** @squad-chief
**Pattern:** HO-TP-001 (Task Anatomy Standard)
**Execution Type:** `Agent`
**Model:** `Opus` (REQUIRED — adaptacao por dominio exige raciocinio)
**Estimated Time:** 10-15min

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-CS-005 | Schema duplica funcionalidade existente no squad | Verificar inventario do audit | VETO - BLOCK. Importar, nao duplicar. |

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | ICS Phase 2 — Domain Mapping |
| **status** | `pending` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | config_extract (from ics-audit), scripts_inventory (from ics-audit) |
| **output** | domain_mapping com primary_entity, paths e session_schema |
| **acceptance_criteria** | 3 criterios testaveis |

---

## Inputs

| Parameter | Type | Required | Source | Validation |
|-----------|------|----------|--------|------------|
| `config_extract` | object | Yes | ics-audit output | Contem workspace_integration fields |
| `scripts_inventory` | object | Yes | ics-audit output | Classifica scripts existentes |

---

## Preconditions

- [ ] ics-audit completo com eligible=true
- [ ] config_extract disponivel com read_paths e write_paths

---

## Steps

### Step 2.1: Identificar Dominio do Squad

Derivar do config_extract:

```yaml
domain_mapping:
  primary_entity: "{business|product|sop|campaign|design_system|...}"
  read_paths: "{do config.yaml workspace_integration.read_paths}"
  write_paths: "{do config.yaml workspace_integration.write_paths}"
  readiness_context_type: "{do config.yaml}"
```

### Step 2.2: Definir Session Schema

Determinar campos obrigatorios e opcionais baseado no dominio:

```yaml
session_schema:
  required:
    - business_slug       # sempre obrigatorio
  optional:
    - product_slug        # se squad trabalha por produto
    - campaign_slug       # se squad usa campanhas (copy, ads)
    - sop_priority        # se squad prioriza por P0/P1/P2 (sop)
    - design_system_slug  # se squad trabalha com DS (design)
```

### Exemplos por Squad

| Squad | primary_entity | session extras | readiness_context_type |
|-------|---------------|----------------|----------------------|
| copy | product + campaign | campaign_slug, asset_type | copy |
| design-system | product + DS | design_system_slug | design |
| aiox-sop | business + backlog | sop_priority, wave | operations |
| brand | business | -- | brand |
| movement | business | -- | movement |

---

## Output Contract

```yaml
domain_mapping:
  primary_entity: "{entity}"
  read_paths: []
  write_paths: []
  readiness_context_type: ""
  session_schema:
    required: ["business_slug"]
    optional: []
```

---

## Acceptance Criteria

- [ ] primary_entity identificada a partir do config_extract
- [ ] session_schema definido com campos required e optional
- [ ] Dominio mapeado e consistente com workspace_integration do config.yaml

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `ics-generate-scripts` |
| **Trigger** | Domain mapping completo |
| **Passes** | domain_mapping, config_extract, scripts_inventory |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-03-26_
_Author: squad-chief_
