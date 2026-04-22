---
task-id: extract-thinking-dna
name: Extract Thinking DNA (Frameworks + Heuristics + Decisions)
version: 2.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Orchestrator -- delegates to 8 atomic sub-tasks for deep extraction"
note: "Exemplos usam copywriting. Substitua pelo seu dominio."
estimated-time: 1-2 hours
complexity: medium

specialist: "@oalanicolas"
specialist_guidance: |
  Extract decision frameworks (SE/ENTAO), heuristics, veto conditions.
  Map recognition_patterns, objection_handling, handoff_triggers.
  Use regra 40/20/40: 40% curadoria, 20% prompt, 40% refinamento.

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise (copy, legal, marketing, etc)"
    - sources: "Minimo 5 fontes com metodologia documentada"

outputs:
  primary:
    - thinking_dna: "Bloco YAML para agent.md com frameworks operacionais"

elicit: true

sub_tasks:
  - etd-recognition-patterns.md
  - etd-discover-frameworks.md
  - etd-extract-heuristics.md
  - etd-decision-architecture.md
  - etd-anti-patterns.md
  - etd-objection-handling.md
  - etd-handoff-triggers.md
  - etd-assemble-output.md
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-thinking-dna
  task_name: Extract Thinking DNA (Frameworks + Heuristics + Decisions)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 1-2h
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''domain'': ''Area de expertise (copy, legal, marketing, etc)''}'
  - '{''sources'': ''Minimo 5 fontes com metodologia documentada''}'
  output:
  - '{''thinking_dna'': ''Bloco YAML para agent.md com frameworks operacionais''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Framework principal com 3+ steps claros [threshold: >= 3]
  - 5+ heuristicas de decisao documentadas [threshold: >= 5]
  - 2+ heuristicas de veto [threshold: >= 2]
  - Pipeline de decisao mapeado [threshold: >= 1]
  - 3+ anti-patterns identificados [threshold: >= 3]
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


# Extract Thinking DNA

> **Objetivo:** Extrair COMO um expert pensa -- seus frameworks, heuristicas e arquitetura de decisao.
>
> **Filosofia:** "Clone minds > create bots" -- Pessoas reais tem skin in the game, suas decisoes foram testadas no mundo real.

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-ETD-001 | Minimum 5 sources with documented methodology must be available before extraction | Verify sources input contains >= 5 items with methodology content | VETO - BLOCK. Run collect-sources to acquire sufficient material before extracting thinking DNA. |
| VETO-ETD-002 | Existing thinking_dna block in agent file must be backed up before modification | Check if target agent.md already contains a thinking_dna section | VETO - BLOCK. Create snapshot of current thinking DNA before overwriting. |
| VETO-ETD-003 | All extracted heuristics and frameworks must be traceable to source evidence | Validate that each framework/heuristic has non-empty evidence or source field | VETO - BLOCK. Remove unsourced entries or find supporting evidence before finalizing output. |

---

## Execution Pipeline

Execute sub-tasks sequentially. Each phase builds on previous outputs.

| Phase | Sub-task | Time | Output |
|-------|----------|------|--------|
| 0 | `etd-recognition-patterns.md` | 10 min | recognition_patterns YAML |
| 1 | `etd-discover-frameworks.md` | 20 min | frameworks YAML |
| 2 | `etd-extract-heuristics.md` | 20 min | heuristics YAML |
| 3 | `etd-decision-architecture.md` | 15 min | decision_architecture YAML |
| 4 | `etd-anti-patterns.md` | 10 min | anti_patterns YAML |
| 5 | `etd-objection-handling.md` | 10 min | objection_handling YAML |
| 6 | `etd-handoff-triggers.md` | 10 min | handoff_triggers YAML |
| Final | `etd-assemble-output.md` | 15 min | Complete thinking_dna block |

---

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-extract-thinking-dna.yaml`

---

## Quality Gate (Final -- enforced by etd-assemble-output)

- [ ] Framework principal com 3+ steps claros
- [ ] 5+ heuristicas de decisao documentadas
- [ ] 2+ heuristicas de veto
- [ ] Pipeline de decisao mapeado
- [ ] 3+ anti-patterns identificados
- [ ] 2+ recognition patterns (o que notam primeiro)
- [ ] 2+ objection responses documentadas
- [ ] 1+ handoff trigger identificado
- [ ] Todas as regras tem "rationale" (o PORQUE)

**Score minimo:** 7/9 -> PASS

---

**Squad Architect | Thinking DNA Extractor v2.0**
*"Clone how they think, not just what they say"*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain; sources
- **Outputs:** Bloco YAML para agent.md com frameworks operacionais
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered [threshold: 0 vetoes triggered]
- [ ] Output artifact produced: Bloco YAML para agent.md com frameworks operacionais [threshold: >= 1]
- [ ] Task output validated against quality standards [threshold: score >= 0.8]
