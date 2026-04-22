# Task: Generate Agent File

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-generate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent-generate
name: Generate Agent File
category: agent-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Fill the agent template (agent-tmpl.md) with persona, commands,
  voice DNA, output examples, and anti-patterns from prior phases.
  Apply voice consistency check. Save agent file to squad path.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_agent_generate
Output: artifact::create_agent_generate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Synthesize all outputs from research, persona, and commands phases into a complete agent file by filling the canonical template. Ensure voice DNA consistency across all sections, generate output examples using the defined vocabulary, create objection algorithms from common mistakes, and produce a file that meets the >= 300 line quality standard.

## Prerequisites

- [ ] `create-agent-research` completed (template + research)
- [ ] `create-agent-persona` completed (persona spec + tier)
- [ ] `create-agent-commands` completed (commands + dependencies + handoffs)

## Inputs

```yaml
inputs:
  - name: research_output
    type: object
    required: true
    source: create-agent-research
    description: "Template, squad path, domain research"

  - name: persona_output
    type: object
    required: true
    source: create-agent-persona
    description: "Name, id, role, tier, scope, voice, quality criteria"

  - name: commands_output
    type: object
    required: true
    source: create-agent-commands
    description: "Commands, capabilities, dependencies, handoffs, synergies"
```

## Workflow

### Step 1: Fill Template -- Level 1 (Identity)

```yaml
fill_level_1:
  template: "templates/agent-tmpl.md"
  sections:
    agent_metadata:
      name: "persona_output.agent_name"
      id: "persona_output.agent_id"
      title: "persona_output.role (short form)"
      icon: "persona_output.icon"
      whenToUse: "persona_output.when_to_use"
    persona:
      role: "persona_output.role + research methodologies"
      style: "persona_output.voice.tone"
      identity: "Synthesized from persona + research"
      focus: "persona_output.scope.does"
```

### Step 2: Fill Template -- Level 2 (Operational)

```yaml
fill_level_2:
  core_principles:
    source: "persona_output.methodology + research best practices"
    count: "5-10 principles"
  commands:
    source: "commands_output.commands"
  quality_standards:
    source: "persona_output.quality + research quality_criteria"
  dependencies:
    source: "commands_output.dependencies"
  knowledge_areas:
    source: "persona_output.expertise_areas"
  capabilities:
    source: "commands_output.capabilities"
```

### Step 3: Fill Template -- Level 3 (Voice DNA)

```yaml
fill_level_3:
  voice_dna:
    vocabulary_always_use: "persona_output.voice.vocabulary_always + research vocabulary"
    vocabulary_never_use: "persona_output.voice.vocabulary_never"
    sentence_starters: "Derived from tone + domain conventions"
    metaphors: "5+ domain-appropriate metaphors from research"
    emotional_states: "persona_output.voice.emotional_range"
```

### Step 4: Fill Template -- Level 4 (Quality)

```yaml
fill_level_4:
  output_examples:
    source: "3+ examples from domain research showing input -> output"
    requirement: "Must use vocabulary.always_use terms"
  objection_algorithms:
    source: "Derived from persona_output.quality.common_mistakes"
    count: "4+ objection/response pairs"
  anti_patterns:
    never_do: "persona_output.quality.common_mistakes + research anti-patterns"
    always_do: "persona_output.methodology + research best practices"
    min_counts: "never_do >= 5, always_do >= 5"
  completion_criteria:
    source: "persona_output.quality.completion_criteria"
```

### Step 5: Fill Template -- Levels 5-6 (Credibility + Integration)

```yaml
fill_levels_5_6:
  credibility:
    source: "Domain authority markers from research"
  handoff_to:
    source: "commands_output.handoff_to (>= 3 scenarios)"
  synergies:
    source: "commands_output.synergies"
```

### Step 6: Apply Voice Consistency

```yaml
voice_consistency:
  checks:
    - "All sections use consistent tone from persona_output.voice.tone"
    - "vocabulary.always_use terms appear across output_examples"
    - "No vocabulary.never_use terms appear in any section"
    - "Signature phrases woven into agent identity and examples"
    - "Metaphors appear in examples"
    - "Sentence starters match emotional_states"
  fix_if_inconsistent:
    - "Replace generic terms with domain vocabulary"
    - "Adjust tone in sections that drift from persona"
```

### Step 7: Save Agent File

```yaml
save_agent:
  path: "squads/{squad_name}/agents/{agent_id}.md"
  post_save:
    - verify_file_written
    - count_lines
```

## Output

```yaml
output:
  agent_file: "squads/{squad_name}/agents/{agent_id}.md"
  lines: N
  sections_complete: "6/6 levels"
  voice_consistency: true|false
  tier: N
  artifact_produced:
    artifact_id: agent-persona
    artifact_template: squads/squad-creator/templates/agent-tmpl.md
    lifecycle_state: draft
```

## Acceptance Criteria

- [ ] Agent file written to `squads/{squad_name}/agents/{agent_id}.md`
- [ ] All 6 template levels filled (identity, operational, voice, quality, credibility, integration)
- [ ] Voice consistency check passes (vocabulary terms in examples, no forbidden terms)
- [ ] Output examples >= 3 using vocabulary.always_use terms
- [ ] Anti-patterns: never_do >= 5, always_do >= 5
- [ ] Agent file >= 300 lines

## Veto Conditions

- Agent file < 300 lines (too short for AIOX quality standard)
- Voice DNA section missing or empty
- Output examples < 3
- Agent references files outside squad path (self-contained rule)
- Agent has > 50% philosophical vs operational content

## Related Documents

- `templates/agent-tmpl.md` -- Agent template
- `create-agent-research.md` -- Research input
- `create-agent-persona.md` -- Persona input
- `create-agent-commands.md` -- Commands input
- `create-agent-validate.md` -- Next phase (validation)
- `create-agent.md` -- Orchestrator task
