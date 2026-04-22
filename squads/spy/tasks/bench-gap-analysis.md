# Task: Gap Analysis & Feature Absorption

## Contrato SINKRA

Domain: `Strategic`

responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- sujeitos, fontes e artefatos upstream conforme `Inputs`
Saida:
- artefatos de benchmark em `docs/bench/`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata
```yaml
id: bench-gap-analysis
name: "Gap Analysis & Feature Absorption"
category: benchmark
agent: bench-analyst
elicit: true
estimated_duration: "15-20min"
description: "Identify competitor features to absorb and generate prioritized roadmap"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Analyze an existing benchmark comparison to identify features AIOX should absorb
from a competitor. Produces feature list, prioritized roadmap, and executable backlog.

## Prerequisites

- [ ] At least a `{competitor}-vs-aiox-comparativo-completo.md` exists in `docs/bench/{competitor}/`
- [ ] Or competitor source available for direct analysis

## Inputs

```yaml
inputs:
  competitor_name:
    type: string
    required: true
    elicit: true
    prompt: "Which competitor to analyze gaps for?"

  focus_areas:
    type: array
    required: false
    default: ["agents", "workflows", "tasks", "tooling", "governance", "hooks", "skills"]
    elicit: true
    prompt: "Which areas to focus on? (all by default)"
```

## Steps

### Step 1: Load Existing Comparison (2min)

1. Check `docs/bench/{competitor}/` for existing artifacts
2. Load comparativo-completo and matrices if available
3. If not available, run `bench-quick-compare` first

### Step 2: Identify Gaps (5min)

For each focus area, identify:

1. **Competitor features without AIOX equivalent:**
   - Feature name and description
   - Category (agent/workflow/task/tooling/governance/hooks/skills)
   - Where it exists in competitor (file/module reference)

2. **Competitor features partially covered by AIOX:**
   - What AIOX has vs what competitor adds
   - Gap description (what's missing)

3. **AIOX differentials (reverse gaps):**
   - Features AIOX has that competitor lacks
   - Important for competitive positioning

### Step 3: Feature Analysis (5min)

For each identified gap, analyze:

```markdown
## Feature: {name}

**O que e:**
{Technical description of what the feature does}

**Codigo/config de referencia:** `{file path in competitor}`

**Valor para AIOX:**
- {Benefit 1}
- {Benefit 2}

**Complexidade:** {Baixa | Media | Alta}
- {Implementation notes}

**Prioridade:** {ALTA | MEDIA | BAIXA}
- {Justification}
```

**Output:** `docs/bench/{competitor}/{competitor}-features-para-aiox.md`

### Step 4: Prioritized Roadmap (3min)

Organize features into implementation phases:

```markdown
## Fase 1: Quick Wins (Baixa complexidade, Alto valor)
- Feature A
- Feature B

## Fase 2: Core Improvements (Media complexidade, Alto valor)
- Feature C
- Feature D

## Fase 3: Advanced Capabilities (Alta complexidade)
- Feature E
- Feature F

## Fase 4: Nice-to-have (Baixa prioridade)
- Feature G
```

**Output:** `docs/bench/{competitor}/roadmap-{competitor}-features-para-aiox.md`

### Step 5: Executable Backlog (3min)

Generate structured backlog:

```json
{
  "generatedAt": "ISO-8601",
  "competitor": "{competitor}",
  "items": [
    {
      "id": "GAP-001",
      "title": "Implement {feature}",
      "description": "...",
      "category": "agent|workflow|task|tooling|governance",
      "priority": "P0|P1|P2|P3",
      "complexity": "LOW|MEDIUM|HIGH",
      "source_reference": "{competitor file/module}",
      "aiox_target": "{where to implement in AIOX}",
      "status": "backlog"
    }
  ]
}
```

**Output:**
- `docs/bench/{competitor}/aiox-gap-closure-backlog-executable.json`
- `docs/bench/{competitor}/aiox-gap-closure-backlog-executable.md`

## Output

| File | Description |
|------|-------------|
| `{competitor}-features-para-aiox.md` | Detailed feature analysis |
| `roadmap-{competitor}-features-para-aiox.md` | Prioritized absorption roadmap |
| `aiox-gap-closure-backlog-executable.json` | Machine-readable backlog |
| `aiox-gap-closure-backlog-executable.md` | Human-readable backlog |
