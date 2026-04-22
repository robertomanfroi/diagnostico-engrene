---
task-id: evd-collect-sources
name: "Voice DNA: Collect & Validate Sources"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
estimated-time: 10 min
complexity: low

inputs:
  required:
    - mind_name: "Nome do expert/mind a clonar"
    - sources: "Mínimo 5 fontes (livros, artigos, entrevistas, podcasts)"

outputs:
  primary:
    - validated_sources: "Lista validada de 5+ fontes com classificação ouro/bronze"

elicit: true
parent_task: extract-voice-dna.md
related_tasks:
  - evd-extract-dimensions.md
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: evd-collect-sources
  task_name: 'Voice DNA: Collect & Validate Sources'
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert/mind a clonar''}'
  - '{''sources'': ''Mínimo 5 fontes (livros, artigos, entrevistas, podcasts)''}'
  output:
  - '{''validated_sources'': ''Lista validada de 5+ fontes com classificação ouro/bronze''}'
  action_items:
  - Identify Priority Sources
  - Web Research (if sources insufficient)
  - Classify Sources
  - Validate Minimum Threshold
  acceptance_criteria:
  - Minimum 5 sources collected [threshold: >= 5]
  - At least 3 sources are tier "ouro" (direct from expert) [threshold: >= 3]
  - At least 2 different source types represented [threshold: >= 2]
  - All sources have title, type, and tier classification [threshold: >= 5]
  - Web research executed if initial sources < 5 [threshold: >= 1]
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


# Task: Voice DNA -- Collect & Validate Sources

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `evd-collect-sources` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `agent` |

## Metadata

- **Parent:** `extract-voice-dna.md`
- **Phase:** 1 of 8
- **Model:** Opus (semantic source evaluation is non-deterministic)

## Purpose

Gather and validate a minimum of 5 high-quality sources for voice DNA extraction. Sources are classified by curadoria quality (ouro vs bronze) and must span multiple formats (books, interviews, articles, talks).

## Prerequisites

- Expert/mind name identified
- Access to source materials or web search capability

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| `mind_name` | string | Yes | Nome do expert/mind a clonar |
| `sources` | list | Yes | Mínimo 5 fontes de tipos variados |

## Workflow / Steps

### Step 1: Identify Priority Sources

```
OBRIGATÓRIO (mínimo 5):
[ ] Livro principal / Obra mais conhecida
[ ] 2-3 Entrevistas longas (podcast, YouTube)
[ ] Artigos/posts escritos pelo próprio
[ ] Palestras/keynotes

BONUS:
[ ] Twitter/X threads
[ ] Newsletters
[ ] Debates/discussões
```

### Step 2: Web Research (if sources insufficient)

Search queries to execute:

```
"{nome}" interview transcript
"{nome}" best quotes
"{nome}" writing style
"{nome}" stories anecdotes
```

### Step 3: Classify Sources

Classify each source as:
- **Ouro:** Written/spoken directly by the expert (books, articles, interviews)
- **Bronze:** Secondary sources (profiles, reviews, summaries about the expert)

### Step 4: Validate Minimum Threshold

**CHECKPOINT:** 5+ fontes validated? --> Proceed to vocabulary extraction.

## Output

```yaml
validated_sources:
  mind_name: "{MIND_NAME}"
  total_count: 0  # Must be >= 5
  sources:
    - title: ""
      type: "book|interview|article|talk|thread|newsletter|debate"
      tier: "ouro|bronze"
      url_or_reference: ""
      language: ""
      estimated_word_count: ""
```

## Acceptance Criteria

- [ ] Minimum 5 sources collected [threshold: >= 5]
- [ ] At least 3 sources are tier "ouro" (direct from expert) [threshold: >= 3]
- [ ] At least 2 different source types represented [threshold: >= 2]
- [ ] All sources have title, type, and tier classification [threshold: >= 5]
- [ ] Web research executed if initial sources < 5 [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EVD-001 | Minimum 5 sources must be available before extraction | Verify sources input contains >= 5 items of varied types | VETO - BLOCK. Run collect-sources to acquire sufficient material. |

## Related Documents

- `extract-voice-dna.md` (parent stub)
- `evd-extract-dimensions.md` (next step)
- `collect-sources.md` (general source collection task)
