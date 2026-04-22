<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: deconstruct-synthesize
  task_name: Deconstruct -- Synthesize
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Extract Patterns
  - Generate Synthesis Report
  acceptance_criteria:
  - At least 3 frameworks identified
  - At least 5 heuristics extracted in SE/ENTAO format
  - Anti-patterns documented with sources
  - Direct citations with verifiable [SOURCE:] tags
  - Meta-insights synthesized from core questions
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


# Task: Deconstruct -- Synthesize

**Task ID:** deconstruct-synthesize
**Parent Task:** `deconstruct.md`
**Purpose:** Synthesize frameworks, heuristics, anti-patterns, and citations from extracted answers
**Execution Type:** Agent
**Model:** Opus
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Deconstruct -- Synthesize |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `extraction` YAML from `deconstruct-extract.md` |
| **output** | Synthesis report with frameworks, heuristics, anti-patterns |
| **action_items** | 2 steps |
| **acceptance_criteria** | 3+ frameworks, 5+ heuristics, anti-patterns documented |

---

## Checkpoint

```yaml
checkpoint_caos_sintese:
  consult: "PARADOXES.clarity_from_chaos"
  question: "Explorei CAOS (muitas perguntas, tangentes) antes de DESTILAR (sintese)?"
  if_explorou: "Sintese rica com base ampla"
  if_filtrou_cedo: "Explorar mais -- tangentes revelam surpresas"
  rationale: "Sintese sem exploracao = obvio. Sintese com exploracao = insight."
```

---

## Workflow

### Step 1: Extract Patterns

From the raw answers, identify:

**Frameworks:** Named approaches, processes, or mental models the expert uses.
- Look for: "I always do X then Y then Z", "my process is...", "I call this..."

**Heuristics:** Decision rules in SE/ENTAO format.
- Look for: "when I see X, I do Y", "the trigger for me is...", "my rule of thumb..."

**Anti-Patterns:** What the expert explicitly rejects.
- Look for: "the worst advice is...", "I never...", "people waste time on..."

**Direct Citations:** Verifiable quotes with source.

### Step 2: Generate Synthesis Report

```yaml
deconstruction_synthesis:
  expert: "{expert_name}"
  date: "{date}"

  frameworks_identified:
    - name: "{framework_name}"
      description: "{what it is}"
      source: "[SOURCE: {reference}]"
      steps: []

  heuristics_extracted:
    - rule: "SE {trigger} -> ENTAO {action}"
      source: "[SOURCE: {reference}]"
      context: "{when to apply}"

  anti_patterns_documented:
    - pattern: "{what to avoid}"
      source: "[SOURCE: {reference}]"
      consequence: "{what happens if you do it}"

  direct_citations:
    - quote: "{exact quote}"
      source: "[SOURCE: {reference}]"
      relevance: "{why it matters}"

  meta_insights:
    core_message: "{billboard answer distilled}"
    unique_belief: "{contrarian belief}"
    key_leverage: "{pareto answer}"
    non_negotiable: "{veto answer}"
```

---

## Completion Criteria

- [ ] At least 3 frameworks identified
- [ ] At least 5 heuristics extracted in SE/ENTAO format
- [ ] Anti-patterns documented with sources
- [ ] Direct citations with verifiable [SOURCE:] tags
- [ ] Meta-insights synthesized from core questions

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of deconstruct.md_

## Acceptance Criteria

- [ ] 3+ frameworks
- [ ] 5+ heuristics
- [ ] anti-patterns documented
