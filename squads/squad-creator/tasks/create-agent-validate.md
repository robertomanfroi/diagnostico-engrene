# Task: Validate Agent and Register

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-validate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent-validate
name: Validate Agent and Register
category: agent-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Run quality gate SC_AGT_001 against the generated agent file,
  fix blocking issues (max 2 iterations), register agent in
  squad config.yaml and README.md, and hand off to publish.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_agent_validate
Output: artifact::create_agent_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Validate the generated agent file against the quality gate checklist
(`checklists/agent-quality-gate.md`), scoring across 6 dimensions. Fix any
blocking issues automatically (up to 2 iterations). On pass, register the
agent in the squad's `config.yaml` and `README.md`, then hand off to the
publish phase for IDE sync and core surface refresh.

## Prerequisites

- [ ] `create-agent-generate` completed (agent file exists)
- [ ] `checklists/agent-quality-gate.md` accessible
- [ ] `data/quality-dimensions-framework.md` accessible
- [ ] `data/decision-heuristics-framework.md` accessible

## Inputs

```yaml
inputs:
  - name: generate_output
    type: object
    required: true
    source: create-agent-generate
    description: "Agent file path, line count, voice consistency status"

  - name: squad_name
    type: string
    required: true
    source: create-agent-research
    description: "Target squad name"
```

## Workflow

### Step 1: Run Quality Gate SC_AGT_001

```yaml
run_quality_gate:
  heuristic_id: SC_AGT_001
  name: "Agent Quality Gate"
  checklist: "checklists/agent-quality-gate.md"
  blocking: true

  blocking_requirements:
    lines: ">= 300"
    output_examples: ">= 3"
    anti_patterns_never_do: ">= 5"
    completion_criteria: "defined"
    handoff_to: "defined"
  mind_clone_blocking:
    voice_dna_vocabulary_always: ">= 5 items"
    voice_dna_vocabulary_never: ">= 3 items"
    note: "voice_dna requirements apply ONLY to mind clones (agents based on real people). Skip for orchestrators and functional agents."

  scoring:
    - dimension: Structure
      weight: 0.25
      check: "All required levels present"
    - dimension: Voice DNA
      weight: 0.15
      check: "Complete with vocabulary (mind clones only, otherwise N/A)"
    - dimension: Examples
      weight: 0.20
      check: "Real, not generic"
    - dimension: Anti-patterns
      weight: 0.15
      check: "Specific to domain"
    - dimension: Integration
      weight: 0.15
      check: "Handoffs defined"
    - dimension: Research
      weight: 0.10
      check: "Traceable to sources"

  threshold: 7.0
  decision:
    IF all_blocking_pass AND score >= 7.0: PROCEED to Step 3
    ELSE: GOTO Step 2
```

### Step 2: Fix Blocking Issues (max 2 iterations)

```yaml
fix_issues:
  max_iterations: 2
  for_each_failure:
    - identify: "What is missing"
    - source: "Where to get it (research, elicitation supplement)"
    - fix: "Add the content"
  common_fixes:
    lines_short:
      - "Expand core_principles with detail"
      - "Add more output_examples"
      - "Expand objection_algorithms"
    missing_voice_dna:
      - "Only required for mind clones (agents based on real people)"
      - "If mind clone: extract from domain research, add vocabulary lists"
      - "If orchestrator/functional: skip — voice_dna not needed"
    few_examples:
      - "Research domain for real examples"
      - "Create based on methodology"
      - "Ensure they show input -> output"
  on_max_iterations: "Save as draft, flag for human review"
```

### Step 3: Register Agent in Squad

```yaml
register_agent:
  update_config_yaml:
    - Add agent entry to agents[] list
    - Add activation shortcut
  update_readme:
    - Add agent to agents table
  verify:
    - config.yaml YAML is valid
    - README.md updated correctly
```

### Step 4: Emit Publish Handoff

```yaml
publish_handoff:
  must_include:
    - squad_name
    - agent_id
    - validation_score
    - registered_in_config: true
    - registered_in_readme: true
  next_phase: "create-agent-publish"
```

## Output

```yaml
output:
  quality_score: "N/10"
  blocking_requirements: "ALL PASS | PARTIAL"
  agent_file: "squads/{squad-name}/agents/{agent-id}.md"
  lines: N
  status: "PASS | DRAFT (flagged for review)"
  config_updated: true
  readme_updated: true
  next_phase: "create-agent-publish"
```

## Acceptance Criteria

- [ ] Quality gate SC_AGT_001 executed with score >= 7.0
- [ ] All blocking requirements pass (lines, voice_dna, examples, anti-patterns, handoffs)
- [ ] Agent registered in squad config.yaml
- [ ] Agent added to squad README.md
- [ ] Publish handoff emitted for IDE sync and core refresh

## Veto Conditions

- Quality score < 7.0 after 2 fix iterations
- Agent file fails self-contained rule (references outside squad path)
- Agent has no SCOPE defined
- Agent has no decision heuristics
- Agent has no output examples

## Related Documents

- `checklists/agent-quality-gate.md` -- Quality gate checklist
- `data/quality-dimensions-framework.md` -- Scoring dimensions
- `data/decision-heuristics-framework.md` -- Quality gate logic
- `create-agent-generate.md` -- Prerequisite (agent file)
- `create-agent.md` -- Orchestrator task
- `create-agent-publish.md` -- Next phase
