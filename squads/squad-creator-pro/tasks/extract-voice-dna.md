---
task-id: extract-voice-dna
name: Extract Voice DNA (Communication & Writing Style)
version: 3.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Extração semântica de padrões de comunicação requer interpretação profunda de linguagem natural - não determinístico"
note: "Exemplos usam copywriting. Substitua pelo seu domínio."
estimated-time: 1-2 hours
complexity: medium
decomposed: true
subtask_count: 3

specialist: "@oalanicolas"
specialist_guidance: |
  Use DNA Mental 8-layer architecture.
  Apply curadoria ouro vs bronze para fontes.
  Extract: power_words, signature_phrases, storytelling, anti-patterns, immune_system.
  Follow Playbook + Framework + Swipe File trinity.

inputs:
  required:
    - mind_name: "Nome do expert/mind a clonar"
    - sources: "Mínimo 5 fontes (livros, artigos, entrevistas, podcasts)"

outputs:
  primary:
    - voice_dna: "Bloco YAML com DNA de comunicação/escrita"

elicit: true
related_tasks:
  - extract-thinking-dna.md
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-voice-dna
  task_name: Extract Voice DNA (Communication & Writing Style)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 1-2h
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert/mind a clonar''}'
  - '{''sources'': ''Mínimo 5 fontes (livros, artigos, entrevistas, podcasts)''}'
  output:
  - '{''voice_dna'': ''Bloco YAML com DNA de comunicação/escrita''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - 10+ power words com [SOURCE:] [threshold: >= 10]
  - 8+ frases assinatura [threshold: >= 8]
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
  executor: Clone
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Extract Voice DNA

> **Objetivo:** Extrair COMO um expert se comunica e escreve.
>
> **Complemento:** Use `extract-thinking-dna.md` para frameworks e decisões.
>
> **Status:** Decomposed into 3 tasks (v3.0.0). De-atomized from 9 to 3.

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EVD-001 | Minimum 5 sources must be available | Verify sources >= 5 items of varied types | VETO - BLOCK. Run collect-sources first. |
| VETO-EVD-002 | Existing voice_dna must be backed up | Check if target agent.md has voice_dna section | VETO - BLOCK. Snapshot before overwriting. |
| VETO-EVD-003 | All entries must have SOURCE citations | Validate [SOURCE: doc, page] format | VETO - BLOCK. Remove uncited entries. |

---

## Execution Pipeline (3 Tasks)

Execute in order. Each task is self-contained with its own inputs, outputs, and acceptance criteria.

| Phase | Task ID | File | Est. Time |
|-------|---------|------|-----------|
| 1. Collect | `evd-collect-sources` | `evd-collect-sources.md` | 10 min |
| 2. Extract | `evd-extract-dimensions` | `evd-extract-dimensions.md` | 45 min |
| 3. Assembly | `evd-assemble-voice-dna` | `evd-assemble-voice-dna.md` | 15 min |

### Dependencies

```
evd-collect-sources
  |
  +---> evd-extract-dimensions (all 7 voice dimensions in single pass)
           |
           +---> evd-assemble-voice-dna (assembly + quality gate)
```

Phase 2 extracts all 7 dimensions (vocabulary, storytelling, writing style, tone, anti-patterns, immune system, contradictions) as sequential steps within a single task. Phase 3 assembles and quality-checks.

---

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-extract-voice-dna.yaml`

---

## Quality Gate (enforced in evd-assemble-voice-dna)

### Minimum Quantities (8/10 required)

- [ ] 10+ power words com [SOURCE:]
- [ ] 8+ frases assinatura
- [ ] 3+ metáforas
- [ ] 3+ histórias/anedotas recorrentes
- [ ] Story structure mapeado
- [ ] Todas dimensões de voz preenchidas (1-10)
- [ ] Tom por contexto definido
- [ ] 5+ anti-patterns de comunicação
- [ ] 2+ rejeições automáticas (immune system)
- [ ] 1+ paradoxo/contradição documentado

### Mandatory Requirements (100% required)

- [ ] TODOS power words têm `source:` com [SOURCE: doc, page]
- [ ] TODAS signature_phrases têm `source:` + `example_usage:`
- [ ] TODOS anti-patterns têm `example_wrong:` + `example_correct:`
- [ ] ZERO conteúdo inventado

---

**Squad Architect | Voice DNA Extractor v2.0**
*"Capture how they communicate, not just what they say"*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; sources
- **Outputs:** Bloco YAML com DNA de comunicação/escrita
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered [threshold: 0 vetoes triggered]
- [ ] Output artifact produced: Bloco YAML com DNA de comunicação/escrita [threshold: >= 1]
- [ ] Task output validated against quality standards [threshold: score >= 0.8]
