---
task: "Extract Knowledge: Source Validation"
task_id: extract-knowledge-source-validation
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Source relevance scoring requires deep semantic comprehension of topic coverage."
haiku_eligible: false
responsavel: "@tim-ferriss"
responsavel_type: agent
atomic_layer: task
elicit: true
phase: discovery
parent_task: extract-knowledge

workflows:
  - wf-extraction-pipeline
config:
  - squad-config
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-knowledge-source-validation
  task_name: Source Validation (BLOCKING)
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
  - '.1: Inventory Sources'
  - '.2: Relevance Classification'
  - '.3: Coverage Validation'
  acceptance_criteria:
  - Mais X paginas/minutos de conteudo
  - Citacoes diretas sobre o tema
  - Exemplos praticos do autor
  - All source files inventoried with metadata (pages/minutes, type)
  - Each source scored on 4 relevance criteria (0-10 scale)
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


# Task: Source Validation (BLOCKING)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-knowledge-source-validation` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |
| **Estimated Time** | `15-30 min` |

## Metadata

| Key | Value |
|-----|-------|
| Parent Task | `extract-knowledge` |
| Phase | 0 (Source Validation) |
| Gate | `SOURCE_COVERAGE` |
| Blocking | Yes -- all downstream phases depend on this |

## Purpose

Validate that source materials are sufficient for knowledge extraction before any extraction work begins. This gate prevents wasted effort on incomplete source sets.

**Principle:** "Se nao tem fonte suficiente, nao comeca."

## Prerequisites

- Source materials must exist at `sources_path`
- `author_name` and `topic` must be provided
- Source files must be readable (PDF, TXT, MD, transcripts)

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| author_name | string | Yes | Author/expert name (e.g., "Alex Hormozi") |
| topic | string | Yes | Specific topic to extract (e.g., "Value Equation") |
| sources_path | path | Yes | Path to source materials (books, transcripts, etc.) |

## Workflow / Steps

### Step 0.1: Inventory Sources

```yaml
action: "List all available source files"
command: "ls -la {sources_path}"
output:
  - file_list
  - total_pages_or_minutes
  - source_types
```

### Step 0.2: Relevance Classification

For each source, evaluate:

| Criterion | Question | Score |
|-----------|----------|-------|
| Direct mention | Source mentions {topic} by name? | 0-3 |
| Process explained | Author explains how to do it? | 0-3 |
| Examples given | Practical examples included? | 0-2 |
| Quotable content | Has usable quotes? | 0-2 |

**Threshold:** Include sources with score >= 5/10

### Step 0.3: Coverage Validation

```yaml
minimum_requirements:
  pages_or_minutes: 5+
  direct_quotes: 3+
  practical_examples: 2+
  framework_identifiable: true

decision:
  GO: "4/4 requirements met"
  CONDITIONAL: "3/4 + acquisition plan"
  NO_GO: "<3/4 -> STOP, get more sources"
```

**Elicit if NO_GO:**
```
Fontes insuficientes para extracao de "{topic}".

Faltam:
- [ ] Mais X paginas/minutos de conteudo
- [ ] Citacoes diretas sobre o tema
- [ ] Exemplos praticos do autor

Opcoes:
1. Fornecer fontes adicionais
2. Pesquisar por mais material (Deep Research)
3. Ajustar escopo do topic
```

## Output

| Output | Type | Description |
|--------|------|-------------|
| source_inventory.yaml | YAML | Inventoried sources with relevance scores and coverage assessment |

## Acceptance Criteria

- [ ] All source files inventoried with metadata (pages/minutes, type) [threshold: >= 1]
- [ ] Each source scored on 4 relevance criteria (0-10 scale) [threshold: >= 4]
- [ ] Sources below threshold (< 5/10) excluded with reason [threshold: score >= 0.8]
- [ ] Coverage validation decision rendered (GO / CONDITIONAL / NO_GO) [threshold: >= 1]
- [ ] `source_inventory.yaml` written to output path [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EKN-001 | Source materials must exist and pass SOURCE_COVERAGE gate before extraction begins | Verify sources_path contains files with relevance score >= 5/10 | VETO - BLOCK. Run collect-sources or provide additional materials before proceeding. |
| VETO-EKN-003 | Zero-invention constraint must be verifiable -- all output claims must have SOURCE citations | Validate anti-invention check is executable against provided sources | VETO - BLOCK. Sources must contain extractable quotes and references before proceeding. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-knowledge.md` | Parent task (stub) |
| `extract-knowledge-framework.md` | Next phase (if GO) |
| `collect-sources.md` | Fallback if NO_GO |
| `auto-acquire-sources.md` | Alternative source acquisition |
