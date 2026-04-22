# Task: Create Squad Agent (Orchestrator)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-agent` |
| **Version** | `4.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: create-agent
name: Create Squad Agent
category: agent-creation
agent: squad-chief
elicit: true
autonomous: false
description: >
  Orchestrator task that creates a domain-specific agent through a 6-phase
  pipeline of atomic tasks. Each phase has single responsibility, clear
  inputs/outputs, and independent validation.
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_agent
Output: artifact::create_agent
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Create a single high-quality agent using template-based elicitation, domain
research, quality validation, and post-create publication. This orchestrator
delegates to 6 atomic tasks in sequence, passing outputs between phases.

**Quality Standard:** AIOX Level (300+ lines, output_examples, anti_patterns). voice_dna required only for mind clones.

> **Note:** For mind-cloned agents based on real experts, use squad-creator-pro with `*clone-mind`.

## Pipeline

```
INPUT (agent_purpose + domain + squad_name)
    |
[Phase 1: RESEARCH]        -> create-agent-research.md
    |                          Load template, validate squad, research domain
[Phase 2: PERSONA]          -> create-agent-persona.md
    |                          Elicit identity, scope, voice, classify tier
[Phase 3: COMMANDS]         -> create-agent-commands.md
    |                          Define commands, capabilities, dependencies, handoffs
[Phase 4: GENERATE]         -> create-agent-generate.md
    |                          Fill template, apply voice consistency, save file
[Phase 5: VALIDATE]         -> create-agent-validate.md
    |                          Quality gate SC_AGT_001, register, handoff summary
[Phase 6: PUBLISH]          -> create-agent-publish.md
    |                          IDE sync, .aiox-sync.yaml, optional core surface refresh
OUTPUT: Agent file + published activation surfaces
```

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `agent_purpose` | string | Yes | What the agent should do |
| `domain` | string | Yes | Domain/area of expertise |
| `squad_name` | string | Yes | Target squad |
| `agent_role` | string | No | Specific role within squad |
| `tier_hint` | integer | No | Suggested tier (0-3) |

## Design Rules (Non-Negotiable)

```yaml
self_contained: "Squad DEVE ser self-contained -- tudo dentro da pasta do squad"
functional_over_philosophical: "Agent deve saber FAZER, nao ser clone perfeito"
curadoria_over_volume: "Menos mas melhor -- 400-800 focused lines > 1500 dispersas"
```

## Veto Conditions

- Agent references files outside squad path
- Agent has > 50% philosophical vs operational content
- Agent has no SCOPE defined
- Agent has no decision heuristics
- Agent has no output examples

## Heuristics

| ID | Name | Phase | Blocking |
|----|------|-------|----------|
| SC_ELC_001 | Elicitation Complete | 2 (Persona) | Yes |
| SC_AGT_001 | Agent Quality Gate | 5 (Validate) | Yes |

## Frameworks Used

- `data/tier-system-framework.md` -- Agent tier classification (Phase 2)
- `data/quality-dimensions-framework.md` -- Agent validation (Phase 5)
- `data/decision-heuristics-framework.md` -- Quality gate logic (Phase 5)

## Atomic Tasks

| Phase | Task | Responsibility |
|-------|------|---------------|
| 1 | `create-agent-research.md` | Template loading, squad validation, domain research |
| 2 | `create-agent-persona.md` | Identity, scope, voice, tier elicitation |
| 3 | `create-agent-commands.md` | Commands, capabilities, dependencies, handoffs |
| 4 | `create-agent-generate.md` | Template filling, voice consistency, file save |
| 5 | `create-agent-validate.md` | Quality gate, registration, handoff summary |
| 6 | `create-agent-publish.md` | IDE sync, .aiox-sync.yaml, optional core surface refresh |

## Outputs

| Output | Location |
|--------|----------|
| Agent File | `squads/{squad_name}/agents/{agent_id}.md` |
| Updated README | `squads/{squad_name}/README.md` |
| Updated Config | `squads/{squad_name}/config.yaml` |
| Published Slash Skill | `.claude/skills/{slashPrefix}/{agent_id}/SKILL.md` |

## Error Handling

```yaml
elicitation_incomplete: "Re-elicit from user, research to supplement gaps"
research_insufficient: "Retry with different queries, expand scope"
validation_fails: "Auto-fix (max 2 iterations), save as draft if unresolvable"
squad_not_exists: "Suggest *create-squad first"
```

---

_Task Version: 4.0.0 (decomposed from v3.0 monolith)_
_Last Updated: 2026-03-26_
