---
task-id: evd-assemble-voice-dna
name: "Voice DNA: Assemble Final Output & Quality Check"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
estimated-time: 15 min
complexity: medium

inputs:
  required:
    - voice_dimensions: "Output from evd-extract-dimensions (all 7 dimension blocks)"
    - mind_name: "Nome do expert"

outputs:
  primary:
    - voice_dna: "Bloco YAML completo com DNA de comunicação/escrita"

elicit: false
parent_task: extract-voice-dna.md
related_tasks:
  - extract-thinking-dna.md
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: evd-assemble-voice-dna
  task_name: 'Voice DNA: Assemble Final Output & Quality Check'
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 15m
  domain: Operational
  input:
  - '{''voice_dimensions'': ''Output from evd-extract-dimensions (all 7 dimension blocks)''}'
  output:
  - '{''voice_dna'': ''Bloco YAML completo com DNA de comunicação/escrita''}'
  action_items:
  - Assemble Voice DNA Block
  - Run Quality Check -- Minimum Quantities
  - Run Quality Check -- Mandatory Requirements
  - Final Verification
  - Backup Check (if modifying existing agent)
  acceptance_criteria:
  - 10+ power words com [SOURCE:] [threshold: >= 10]
  - 8+ frases assinatura (não apenas 5) [threshold: >= 8]
  - 3+ metáforas [threshold: >= 3]
  - 3+ histórias/anedotas recorrentes [threshold: >= 3]
  - Story structure mapeado [threshold: >= 1]
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


# Task: Voice DNA -- Assemble Final Output & Quality Check

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `evd-assemble-voice-dna` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `agent` |

## Metadata

- **Parent:** `extract-voice-dna.md`
- **Phase:** Assembly (post-extraction)
- **Model:** Opus (final assembly and quality validation)

## Purpose

Assemble all extracted voice DNA components into the final unified YAML block and run the quality check to ensure minimum thresholds and mandatory requirements are met.

## Prerequisites

- `evd-collect-sources` completed -- sources validated
- `evd-extract-dimensions` completed -- all 7 voice dimensions extracted:
  - vocabulary (power words, phrases, metaphors, rules)
  - storytelling (stories, anecdotes, examples, structure)
  - writing_style (structure, devices, formatting, patterns)
  - tone (dimensions, contextual tone, identity statement)
  - anti_patterns (never-say, never-do, rejected styles)
  - immune_system (rejections, boundaries, defenses)
  - voice_contradictions (paradoxes, inconsistencies, preservation)

## Inputs

The `voice_dimensions` output from `evd-extract-dimensions` (contains all 7 dimension blocks).

## Workflow / Steps

### Step 1: Assemble Voice DNA Block

Merge all phase outputs into the unified structure:

```yaml
# =====================================================
# VOICE DNA - {MIND_NAME}
# Focus: Communication & Writing Style
# Extracted: {DATE}
# =====================================================

voice_dna:
  identity_statement: ""  # From evd-extract-dimensions Step 4

  vocabulary:       # From evd-extract-dimensions Step 1
    power_words: []
    signature_phrases: []
    metaphors: []
    rules: {}

  storytelling:     # From evd-extract-dimensions Step 2
    recurring_stories: []
    personal_anecdotes: []
    favorite_examples: []
    story_structure: {}

  writing_style:    # From evd-extract-dimensions Step 3
    structure: {}
    sentence_patterns: []
    rhetorical_devices: {}
    formatting: {}

  tone:             # From evd-extract-dimensions Step 4
    dimensions: {}
    by_context: {}

  anti_patterns:    # From evd-extract-dimensions Step 5
    never_say: []
    never_do: []
    rejected_styles: []

  immune_system:    # From evd-extract-dimensions Step 6
    automatic_rejections: []
    emotional_boundaries: []
    fierce_defenses: []

  voice_contradictions:  # From evd-extract-dimensions Step 7
    paradoxes: []
    authentic_inconsistencies: []
    preservation_note: ""
```

### Step 2: Run Quality Check -- Minimum Quantities

- [ ] 10+ power words com [SOURCE:]
- [ ] 8+ frases assinatura (não apenas 5)
- [ ] 3+ metáforas
- [ ] 3+ histórias/anedotas recorrentes
- [ ] Story structure mapeado
- [ ] Todas dimensões de voz preenchidas (1-10)
- [ ] Tom por contexto definido
- [ ] 5+ anti-patterns de comunicação
- [ ] 2+ rejeições automáticas (immune system)
- [ ] 1+ paradoxo/contradição documentado

### Step 3: Run Quality Check -- Mandatory Requirements

- [ ] TODOS power words têm `source:` com [SOURCE: doc, page]
- [ ] TODAS signature_phrases têm `source:` com [SOURCE: doc, page]
- [ ] TODAS signature_phrases têm `example_usage:` (copy NOVO, não citação)
- [ ] TODOS anti-patterns têm `example_wrong:` + `example_correct:`
- [ ] ZERO conteúdo inventado - apenas extraído das fontes

### Step 4: Final Verification

- [ ] Posso rastrear cada claim até uma fonte específica?
- [ ] Os example_usage são copy NOVO (não apenas repetir a citação)?
- [ ] Os example_correct soam como o expert falaria?

**Score mínimo:** 8/10 quantidades + 100% requisitos de qualidade --> PASS

### Step 5: Backup Check (if modifying existing agent)

If target agent.md already contains a voice_dna section, create snapshot before overwriting.

## Output

The complete `voice_dna:` YAML block ready for insertion into the agent file.

## Acceptance Criteria

- [ ] All 7 dimension outputs (from evd-extract-dimensions) merged into single unified block [threshold: >= 7]
- [ ] Minimum quantities checklist: 8/10 items pass [threshold: >= 8]
- [ ] Mandatory requirements: 100% pass (no exceptions) [threshold: score >= 0.8]
- [ ] Final verification: all 3 checks pass [threshold: >= 3]
- [ ] Existing voice_dna backed up if applicable (VETO-EVD-002) [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EVD-002 | Existing voice_dna block must be backed up before modification | Check if target agent.md already contains a voice_dna section | VETO - BLOCK. Create snapshot before overwriting. |
| VETO-EVD-003 | All entries must have SOURCE citations | Validate every vocabulary entry has non-empty source field | VETO - BLOCK. Remove uncited entries or find supporting references. |

## Related Documents

- `extract-voice-dna.md` (parent stub)
- `extract-thinking-dna.md` (complementary: frameworks and decisions)
