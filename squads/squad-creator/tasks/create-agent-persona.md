# Task: Define Agent Persona

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-persona` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent-persona
name: Define Agent Persona
category: agent-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Elicit core identity, scope, expertise, style, voice DNA,
  and quality criteria from the user to define the agent persona.
  Classifies agent tier using tier-system-framework.md.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_agent_persona
Output: artifact::create_agent_persona
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Gather all persona-defining information through structured elicitation: identity (name, role, icon), scope (does/does-not), expertise areas, methodology, voice DNA (tone, vocabulary, signature phrases, emotional range), and quality criteria. Classify the agent tier. This phase transforms user intent into a structured persona specification ready for template filling.

## Prerequisites

- [ ] `create-agent-research` completed (template loaded, research available)
- [ ] squad-chief agent is active
- [ ] `data/tier-system-framework.md` accessible

## Inputs

```yaml
inputs:
  - name: research_output
    type: object
    required: true
    source: create-agent-research
    description: "Output from research phase (template, squad, domain research)"

  - name: agent_purpose
    type: string
    required: true
    source: user
    description: "What the agent should do"

  - name: tier_hint
    type: integer
    required: false
    source: user
    description: "Suggested tier 0-3 (validated against decision tree)"
```

## Workflow

### Step 1: Elicit Core Identity

```yaml
elicit_identity:
  questions:
    - agent_name: "What should this agent be called?"
    - agent_id: "Short kebab-case identifier (auto-derived from name)"
    - role_description: "Primary role in 1-2 sentences"
    - icon: "Emoji that represents this agent"
    - when_to_use: "When should users activate this agent?"
  auto_derive:
    - agent_id from agent_name (kebab-case)
    - title from role_description (short form)
```

### Step 2: Elicit Scope and Expertise

```yaml
elicit_scope:
  questions:
    - primary_tasks: "3-5 main tasks this agent performs"
    - out_of_scope: "3+ things this agent does NOT do"
    - expertise_areas: "Specific knowledge domains"
    - methodology: "Methodology or framework to follow"
    - tools_and_dependencies: "Tools or data needed"
  optional:
    - reference_experts: "Specific experts or methodologies to draw from"
    - existing_standards: "Existing quality standards for this domain"
```

### Step 3: Elicit Style and Voice

```yaml
elicit_voice:
  questions:
    - communication_tone: "How should this agent communicate?"
    - vocabulary_always: "5+ domain terms to always use"
    - vocabulary_never: "3+ terms to avoid"
    - signature_phrases: "3-5 catchphrases or signature expressions"
    - emotional_range: "Emotional states to express"
  fallback:
    action: "Derive voice from domain research if user input is minimal"
```

### Step 4: Elicit Quality Criteria

```yaml
elicit_quality:
  questions:
    - completion_criteria: "How to know when the task is done well"
    - common_mistakes: "Most common mistakes in this domain"
    - quality_checklist: "What to check before delivering output"
    - handoff_triggers: "When to hand off to another agent or human"
```

### Step 5: Classify Tier

```yaml
classify_tier:
  framework: "data/tier-system-framework.md"
  decision_tree:
    - IF diagnosis/analysis FIRST: tier 0 (Foundation)
    - ELSE IF primary executor with core methodology: tier 1 (Master)
    - ELSE IF creates/systematizes frameworks: tier 2 (Systematizer)
    - ELSE IF format/channel specialist: tier 3 (Format specialist)
    - ELSE IF validation/checklist tool: tier "tools" (Utility)
  override: "Use tier_hint if provided, validate against tree"
```

### Checkpoint SC_ELC_001

```yaml
heuristic_id: SC_ELC_001
name: "Elicitation Complete"
blocking: true
criteria:
  - agent_name defined
  - role_description defined
  - primary_tasks >= 3
  - out_of_scope >= 3
  - methodology defined or research_needed flagged
```

## Output

```yaml
output:
  agent_name: "{Agent Name}"
  agent_id: "{agent-id}"
  role: "{role description}"
  tier: N
  scope:
    does: ["task1", "task2", "task3"]
    does_not: ["exclusion1", "exclusion2", "exclusion3"]
  methodology: "{methodology or 'research_needed'}"
  voice:
    tone: "{tone}"
    vocabulary_always: ["term1", "term2", "term3", "term4", "term5"]
    vocabulary_never: ["term1", "term2", "term3"]
    signature_phrases: ["phrase1", "phrase2", "phrase3"]
    emotional_range: "{emotional states}"
  quality:
    completion_criteria: "{criteria}"
    common_mistakes: ["mistake1", "mistake2"]
    handoff_triggers: ["trigger1", "trigger2"]
  checkpoint_SC_ELC_001: PASS
```

## Acceptance Criteria

- [ ] Agent name, id, role, icon, and whenToUse defined
- [ ] Primary tasks >= 3 and out-of-scope >= 3
- [ ] Methodology defined (or flagged for research supplement)
- [ ] Voice DNA elicited: tone, vocabulary (always >= 5, never >= 3), signature phrases
- [ ] Quality criteria gathered: completion, mistakes, handoffs
- [ ] Tier classified using tier-system-framework.md
- [ ] Checkpoint SC_ELC_001 passes

## Veto Conditions

- Checkpoint SC_ELC_001 fails (agent_name or role undefined, tasks < 3, scope < 3)
- User unable to define minimum scope after 2 elicitation rounds

## Related Documents

- `data/tier-system-framework.md` -- Tier classification framework
- `create-agent-research.md` -- Prerequisite (research output)
- `create-agent-commands.md` -- Next phase (commands/capabilities)
- `create-agent.md` -- Orchestrator task
