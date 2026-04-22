---
task-id: extract-implicit-scan
name: "Initial Scan for Implicit Knowledge"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Detecting logical leaps, undefined concepts, and strategic absences requires deep reasoning. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - source_corpus: "Conteudo a analisar (livro, aula, conversa, codigo, processo)"
    - source_type: "Tipo de conteudo (livro | aula | conversa | codigo | processo | entrevista)"
    - scope_boundaries: "Limites do escopo de extracao"
  optional:
    - prior_extractions: "Extracoes anteriores para triangulacao"

outputs:
  primary:
    - scan_markers: "Lista de pontos marcados com tipo e localizacao no conteudo"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit-scan
  task_name: Initial Scan for Implicit Knowledge
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''source_corpus'': ''Conteudo a analisar (livro, aula, conversa, codigo, processo)''}'
  - '{''source_type'': ''Tipo de conteudo (livro | aula | conversa | codigo | processo
    | entrevista)''}'
  - '{''scope_boundaries'': ''Limites do escopo de extracao''}'
  - '{''prior_extractions'': ''Extracoes anteriores para triangulacao''}'
  output:
  - '{''scan_markers'': ''Lista de pontos marcados com tipo e localizacao no conteudo''}'
  action_items:
  - Validate Inputs
  - Select Detection Heuristics by Source Type
  - Execute Full-Content Scan
  - Mark and Catalog Points
  - Generate Scan Summary
  acceptance_criteria:
  - All required inputs validated before scanning
  - Detection heuristics adapted to source type
  - Complete content scanned (no sections skipped)
  - 'Each marker includes location evidence `[SOURCE: minuto/pagina]'
  - Markers classified by signal type and potential axis
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


# Task: Initial Scan for Implicit Knowledge

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `extract-implicit-scan` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `extract-implicit` (orchestrator stub)
- **Sequence:** Phase 1 of 5
- **Next Task:** `extract-implicit-analyze`

## Purpose

Read or listen to the complete source content and mark all points where implicit knowledge may be hiding. This is a first-pass scan -- breadth over depth. Identify logical leaps, undefined concepts, rapid decisions, and conspicuous absences.

## Prerequisites

- Source corpus must be explicitly defined (VETO-EIM-001)
- If target output file exists, backup must be created (VETO-EIM-002)

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `source_corpus` | Yes | Conteudo a analisar |
| `source_type` | Yes | Tipo de conteudo para adaptar sinais de deteccao |
| `scope_boundaries` | Yes | Limites claros do escopo |
| `prior_extractions` | No | Extracoes anteriores para cruzamento |

## Workflow / Steps

### Step 1: Validate Inputs

Confirm `source_corpus`, `source_type`, and `scope_boundaries` are provided. If any missing, VETO-BLOCK per VETO-EIM-001.

### Step 2: Select Detection Heuristics by Source Type

Load the detection heuristic set based on `source_type`:

| Tipo | Sinais Especificos |
|------|-------------------|
| **Livro** | Premissas do autor, frameworks nao nomeados, vieses disciplinares |
| **Aula** | O que o instrutor assume que voce sabe, atalhos de expert |
| **Conversa** | Decisoes por omissao, requisitos implicitos, riscos ignorados |
| **Codigo** | Convencoes nao documentadas, razoes de design choices |
| **Processo** | Conhecimento tribal, "todo mundo sabe que...", edge cases |
| **Entrevista** | Heuristicas do expert, padroes de decisao, anti-patterns vividos |

### Step 3: Execute Full-Content Scan

Read the complete source content. For each passage, check for these universal signals:

**Logical Leaps:**
- Jumps from A to C without B
- "Obviamente..." / "Claro que..."
- Justificativa circular

**Undefined Concepts:**
- Terms used without definition
- Acronyms assumed known
- Frameworks referenced but not named

**Rapid Decisions:**
- "Vamos fazer X" without alternatives
- Instant rejections without explanation
- "Meu instinto diz..."

**Conspicuous Absences:**
- "E se X?" never asked
- Failure scenarios not discussed
- Dependencies not mapped
- Competitors/alternatives ignored

**Evasion Signals:**
- Generic answers to specific questions
- Topic changes after direct questions
- "Depende" without decision framework
- Humor/irony to deflect sensitive topics

### Step 4: Mark and Catalog Points

For each detected point, record:

```yaml
scan_markers:
  - id: "SCAN-001"
    location: "[SOURCE: minuto/pagina]"
    signal_type: "logical_leap | undefined_concept | rapid_decision | absence | evasion"
    raw_evidence: "{trecho ou descricao}"
    potential_axis: "premissa | heuristica | ponto_cego | decisao_implicita | evasao"
    confidence: "alta | media | baixa"
```

### Step 5: Generate Scan Summary

```yaml
scan_summary:
  total_markers: 0
  by_signal_type:
    logical_leap: 0
    undefined_concept: 0
    rapid_decision: 0
    absence: 0
    evasion: 0
  by_potential_axis:
    premissa: 0
    heuristica: 0
    ponto_cego: 0
    decisao_implicita: 0
    evasao: 0
```

## Output

```yaml
scan_markers:
  markers: []
  summary:
    total_markers: 0
    by_signal_type: {}
    by_potential_axis: {}
  source_metadata:
    source_type: ""
    scope: ""
    scan_date: ""
```

## Acceptance Criteria

- [ ] All required inputs validated before scanning [threshold: >= 3]
- [ ] Detection heuristics adapted to source type [threshold: >= 1]
- [ ] Complete content scanned (no sections skipped) [threshold: score >= 0.8]
- [ ] Each marker includes location evidence `[SOURCE: minuto/pagina]` [threshold: score >= 0.8]
- [ ] Markers classified by signal type and potential axis [threshold: >= 1]
- [ ] Scan summary generated with counts [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EIM-001 | Source corpus must be explicitly defined before extraction | Verify input includes at least one concrete source and scope boundaries | VETO - BLOCK. Request explicit source corpus and scope. |
| VETO-EIM-002 | Existing extraction artifact must be backed up before overwrite | Check if target output file already exists | VETO - BLOCK. Create backup snapshot before writing. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-implicit.md` | Parent orchestrator |
| `extract-implicit-analyze.md` | Next phase (deep analysis) |
