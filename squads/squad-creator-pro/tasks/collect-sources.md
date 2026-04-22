---
task-id: collect-sources
name: "Collect & Validate Sources for Mind Cloning"
version: 3.0.0
execution_type: Orchestrator
model: Sonnet
model_rationale: "Orchestrator stub — delegates to atomic sub-tasks. Sonnet for routing decisions."
haiku_eligible: false
note: "Decomposed from v2.3.0 monolith (548 lines) into 5 atomic tasks."
estimated-time: 30-60 min
complexity: medium

specialist: "@oalanicolas"
specialist_guidance: |
  Use DNA Mental source curation methodology:
  - Classify sources as OURO (gold) vs BRONZE quality
  - OURO: Direct from expert (books, interviews, courses) = Tier 0-1
  - BRONZE: About expert (summaries, articles) = Tier 2-3
  - Apply 40/20/40 rule: 40% curadoria, 20% prompt, 40% refinamento
  - For complex source assessment, invoke: @oalanicolas *assess-sources

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
  optional:
    - user_materials_path: "Caminho para materiais do usuario (Tier 0)"

outputs:
  primary:
    - sources_inventory: "Lista validada de fontes com classificacao e decisao GO/CONDITIONAL/NO-GO"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: collect-sources
  task_name: Collect & Validate Sources for Mind Cloning
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 30-60m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''domain'': ''Area de expertise''}'
  - '{''user_materials_path'': ''Caminho para materiais do usuario (Tier 0)''}'
  output:
  - '{''sources_inventory'': ''Lista validada de fontes com classificacao e decisao
    GO/CONDITIONAL/NO-GO''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 10+ fontes totais identificadas [threshold: >= 10]
  - 5+ fontes Tier 1 (primarias) [threshold: >= 5]
  - 3+ tipos diferentes de fonte [threshold: >= 3]
  - 5+ horas OU 200+ paginas de conteudo [threshold: >= 5h OR >= 200p]
  - Framework principal triangulado (3+ fontes) [threshold: >= 3]
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


# Collect & Validate Sources

> **Principio Core:** "Single source = hypothesis; three sources = pattern"
>
> **Regra:** NUNCA prosseguir para extracao sem validar fontes suficientes.

---

## Pipeline (5 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `collect-sources-discover` | Discover Sources | 15 min |
| 2 | `collect-sources-classify` | Classify by Tier | 10 min |
| 3 | `collect-sources-validate` | Validate Coverage & Triangulation | 10 min |
| 4 | `collect-sources-gap-analysis` | Gap Analysis & Acquisition Plan | 5 min |
| 5 | `collect-sources-quality-gate` | Quality Gate GO/NO-GO & Output | 5 min |

---

## Canonical Owner

- `workflows/wf-collect-sources.yaml` é o owner canônico do pipeline atômico de coleta e validação de fontes.

---

## Execution Flow

```
collect-sources-discover
  │ discovered_sources
  ▼
collect-sources-classify
  │ sources_by_tier
  ▼
collect-sources-validate
  │ coverage_report
  ▼
collect-sources-gap-analysis
  │ gap_analysis
  ▼
collect-sources-quality-gate
  │ sources_inventory (FINAL OUTPUT)
  ▼
[DONE or LOOP to Phase 1 if NO-GO]
```

---

## Veto Conditions (Consolidated)

| ID | Condition | Phase | Result |
|----|-----------|-------|--------|
| VETO-CSR-001 | `mind_name` and `domain` must be provided | Phase 1 | BLOCK |
| VETO-CSR-002 | Existing inventory must be backed up before overwrite | Phase 1 | BLOCK |
| VETO-CSR-003 | Quality gate must not be bypassed | Phase 5 | BLOCK |
| VETO-CSR-004 | `min_sources` and `domain_validation` must pass | Phase 3/5 | BLOCK |

---

## Fallback Chain (Phase 1 Internal)

```
Step 1: User Materials → Tier 0
Step 2: Auto-Acquire (auto-acquire-sources.md) → >= 10?
Step 3: Manual Web Search → >= 10?
Step 4: FAIL — Expert too obscure
```

---

## Quality Check (Summary)

- [ ] 10+ fontes totais identificadas
- [ ] 5+ fontes Tier 1 (primarias)
- [ ] 3+ tipos diferentes de fonte
- [ ] 5+ horas OU 200+ paginas de conteudo
- [ ] Framework principal triangulado (3+ fontes)
- [ ] Decisao GO ou CONDITIONAL com plano

**BLOCKING:** Se <4 checks passam, resultado e NO-GO.

---

**Squad Architect | Source Collector v3.0**

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain
- **Outputs:** Lista validada de fontes com classificacao e decisao GO/CONDITIONAL/NO-GO
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered [threshold: 0 vetoes triggered]
- [ ] Output artifact produced: Lista validada de fontes com classificacao e decisao GO/CONDITIONAL/NO-GO [threshold: >= 1]
- [ ] Task output validated against quality standards [threshold: score >= 0.8]
