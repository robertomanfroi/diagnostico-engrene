---
task-id: validate-extraction-checklist
name: "Run 11-Point Checklist"
version: 1.0.0
execution_type: Worker
model: Haiku
model_rationale: "Checklist validation is deterministic counting and pattern matching."
haiku_eligible: true
estimated-time: 10 min
complexity: low

inputs:
  required:
    - expert_name: "Nome do expert avaliado"
    - extraction_files: "Arquivos de extracao a validar"

outputs:
  primary:
    - checklist_results: "11 items scored with evidence"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-extraction-checklist
  task_name: Run 11-Point Checklist
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 10m
  domain: Operational
  input:
  - '{''expert_name'': ''Nome do expert avaliado''}'
  - '{''extraction_files'': ''Arquivos de extracao a validar''}'
  output:
  - '{''checklist_results'': ''11 items scored with evidence''}'
  action_items:
  - Validate Items 1-9
  - Record Results
  - Fail Actions per Item
  acceptance_criteria:
  - All 9 items evaluated with evidence
  - Counts are verified (not estimated)
  - Fail actions documented for each failed item
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
  coherence_threshold: 0.95
  error_behavior: raise
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Run 11-Point Checklist

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-extraction-checklist` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

- **Parent Task:** `validate-extraction` (orchestrator stub)
- **Sequence:** Phase 1 of 3
- **Previous Task:** None
- **Next Task:** `validate-extraction-adversarial`

## Purpose

Executar os primeiros 9 itens do checklist de validacao, verificando contagens e presenca de elementos obrigatorios.

## Workflow / Steps

### Step 1: Validate Items 1-9

| # | Criterio | Threshold | How to Check |
|---|----------|-----------|-------------|
| 1 | Citacoes diretas com `[SOURCE:]` | >= 15 | `grep -c "\[SOURCE:" {arquivo}` |
| 2 | Signature phrases verificaveis | >= 5 | Count phrases appearing in 2+ sources |
| 3 | Thinking DNA com decision architecture | Mapeada | Check `decision_architecture:` or `pipeline:` exists |
| 4 | Heuristics com contexto (QUANDO aplicar) | Cada uma | Each heuristic has `when_to_use:` field |
| 5 | Anti-patterns documentados do EXPERT | Nao genericos | Each has [SOURCE:] and expert-specific justification |
| 6 | Conceitos marcados como "inferido" | Zero | Search for `[INFERRED]` -- must be zero |
| 7 | Pareto ao Cubo aplicado (0.8% identificado) | Documentado | Check documentation of expert's unique genius |
| 8 | Evasion Scan executado (silencios mapeados) | Executado | At least 1 evasion identified |
| 9 | Paradigm Inversions documentadas | >= 1 | Format: `SE {campo diz X} -> ENTAO {expert faz Y}` |

### Step 2: Record Results

For each item:

```yaml
checklist_results:
  - item: 1
    criterio: "Citacoes [SOURCE:]"
    threshold: ">= 15"
    actual: {count}
    status: "PASS|FAIL"
    evidence: "{how verified}"
```

### Step 3: Fail Actions per Item

| Item | Se FAIL | Acao |
|------|---------|------|
| 1 | Citacoes < 15 | Buscar mais entrevistas/podcasts |
| 2 | Phrases < 5 | Procurar padroes repetidos |
| 3 | Decision arch faltando | Focar em "como decide" |
| 4 | Heuristics sem contexto | Documentar QUANDO aplicar |
| 5 | Anti-patterns genericos | Buscar citacoes do expert |
| 6 | Inferencias presentes | Buscar [SOURCE:] ou deletar |
| 7 | 0.8% nao identificado | Executar task find-0-8.md |
| 8 | Evasion Scan nao feito | Analisar perguntas evitadas |
| 9 | Zero inversoes | Buscar onde expert contradiz o campo |

## Output

```yaml
checklist_results: [{ 9 items with status and evidence }]
items_passed: 0
items_failed: 0
```

## Acceptance Criteria

- [ ] All 9 items evaluated with evidence
- [ ] Counts are verified (not estimated)
- [ ] Fail actions documented for each failed item

## Related Documents

| Document | Relationship |
|----------|-------------|
| `validate-extraction.md` | Parent orchestrator |
| `validate-extraction-adversarial.md` | Next phase |
| `checklists/sop-validation.md` | Checklist reference |
