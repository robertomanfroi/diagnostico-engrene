# Task: Research Domain and Load Templates

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent-research` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent-research
name: Research Domain and Load Templates
category: agent-creation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Load the agent template, validate that the target squad exists,
  identify required template sections, and perform domain research
  to gather best practices, frameworks, vocabulary, and anti-patterns.
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_agent_research
Output: artifact::create_agent_research
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Prepare the foundation for agent creation by loading the canonical template (`templates/agent-tmpl.md`), validating the target squad path, identifying all 18 required template sections across 6 levels, and conducting web research to gather domain-specific methodologies, vocabulary, and anti-patterns. This phase ensures all raw material is available before elicitation and generation begin.

## Prerequisites

- [ ] Target squad exists at `squads/{squad_name}/`
- [ ] `templates/agent-tmpl.md` is accessible
- [ ] WebSearch tool available (for domain research)
- [ ] `squads/squad-creator/protocols/ai-first-governance.md` applied

## Inputs

```yaml
inputs:
  - name: agent_purpose
    type: string
    required: true
    source: user
    description: "What the agent should do (e.g., 'Create sales pages')"

  - name: domain
    type: string
    required: true
    source: user
    description: "Domain/area of expertise (e.g., 'copywriting')"

  - name: squad_name
    type: string
    required: true
    source: user
    description: "Target squad (e.g., 'copy')"
```

## Workflow

### Step 1: Validate Target Squad

```yaml
validate_squad:
  check_path: "squads/{squad_name}/"
  load_config: "config.yaml"
  on_not_exists:
    option_1: "Create squad first with *create-squad"
    option_2: "Create agent standalone (not recommended)"
  decision:
    IF squad exists: PROCEED
    ELSE: ASK user to create squad first
```

### Step 2: PRO Detection

```yaml
pro_detection:
  check: "squads/squad-creator-pro/config.yaml exists"
  if_yes_and_active: "Delegate to pro workflow override"
  if_no: "Continue with base version"
```

### Step 3: Load Agent Template

```yaml
load_template:
  file: "templates/agent-tmpl.md"
  required: true
  extract_sections:
    level_1_identity:
      - activation_notice
      - ide_file_resolution
      - activation_instructions
      - agent_metadata (name, id, title, icon, whenToUse)
      - persona (role, style, identity, focus)
    level_2_operational:
      - core_principles (5-10)
      - commands
      - quality_standards
      - dependencies (tasks, templates, checklists, data)
      - knowledge_areas
      - capabilities
    level_3_voice: [voice_dna]
    level_4_quality: [output_examples, objection_algorithms, anti_patterns, completion_criteria]
    level_5_credibility: [credibility]
    level_6_integration: [handoff_to, synergies]
  output:
    template_loaded: true
    sections_to_fill: 18
```

### Step 4: Research Domain Best Practices

```yaml
domain_research:
  method: "WebSearch"
  queries:
    - "{domain} best practices {agent_purpose}"
    - "{domain} methodology framework"
    - "{domain} expert techniques {primary_tasks}"
    - "{domain} common anti-patterns mistakes"
  extract:
    - methodologies: "Step-by-step processes"
    - frameworks: "Decision frameworks and mental models"
    - vocabulary: "Standard domain terminology"
    - anti_patterns: "Common mistakes and what to avoid"
    - quality_criteria: "How experts evaluate work"
  quality_criteria:
    min_unique_sources: 3
    requires_actionable_content: true
    max_inference_ratio: 0.30
```

### Step 5: AI-First Governance Gate

```yaml
governance:
  - Map "Existing -> Gap -> Decision" before creating agent
  - Validate canonical sources (squad config/tasks/workflows/data)
  - Mark dependency status: implemented | partial | concept
  - List unresolved items
```

## Output

```yaml
output:
  squad_name: "{squad-name}"
  pack_path: "squads/{squad-name}/"
  template_loaded: true
  sections_to_fill: 18
  research_summary:
    sources_used: N
    methodologies_found: N
    vocabulary_extracted: N
    anti_patterns_found: N
  pro_mode: false
  governance_gate: PASS
```

## Acceptance Criteria

- [ ] Target squad path validated and config.yaml loaded
- [ ] Agent template loaded with all 18 sections identified
- [ ] Domain research performed with >= 3 unique sources
- [ ] Research extracted actionable methodologies, vocabulary, and anti-patterns
- [ ] AI-First Governance gate completed
- [ ] PRO detection executed

## Veto Conditions

- Squad path does not exist and user declines creation
- Template file `agent-tmpl.md` not found
- Research yields 0 actionable sources after retry

## Related Documents

- `templates/agent-tmpl.md` -- Agent template
- `protocols/ai-first-governance.md` -- Governance protocol
- `data/tier-system-framework.md` -- Tier classification (used in later phase)
- `create-agent.md` -- Orchestrator task
