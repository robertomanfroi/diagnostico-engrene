# Task: Feature Absorption Roadmap (Autonomous)

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
id: bench-absorb
name: "Feature Absorption Roadmap"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "12-18min"
description: "Deep analysis of competitor-only features and structured roadmap for AIOX absorption"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Identify specific features from a competitor that AIOX lacks, analyze each one's
value and complexity, and produce a prioritized absorption roadmap with executable backlog.

## Prerequisites

- Comparativo completo exists: `docs/bench/{competitor}/{competitor}-vs-aiox-comparativo-completo.md`
- If not, run `bench-quick-compare` first
- Competitor repo cloned locally at `../bench/{competitor}/`

## Reference

See `docs/bench/pai/pai-features-para-aiox.md` and `docs/bench/pai/roadmap-pai-features-para-aiox.md` for output format.

---

## CRITICAL: Local Clone Rule

**Feature analysis MUST reference the locally cloned competitor repository.**

```
Competitor source: ../bench/{competitor}/ (cloned by earlier pipeline phases)
If clone does not exist: HALT - run bench-quick-compare or bench-framework first.
All Grep/Read operations on competitor files target ../bench/{competitor}/.
NEVER invent file paths or content. NEVER estimate.
```

---

## Step 1: Extract Competitor-Only Features

```
ACTION: Read("docs/bench/{competitor}/{competitor}-vs-aiox-comparativo-completo.md")
EXTRACT: All items listed under "Gaps {competitor} (sem equivalente AIOX)"

ACTION: Scan local clone for feature categories:
  Grep("../bench/{competitor}/", "hook|lifecycle|event", type="md")  → hooks_features[]
  Grep("../bench/{competitor}/", "skill|plugin|extension", type="md") → extensibility_features[]
  Grep("../bench/{competitor}/", "rating|feedback|learn", type="md")  → learning_features[]
  Grep("../bench/{competitor}/", "voice|speech|tts", type="md")       → ux_features[]
  Grep("../bench/{competitor}/", "test|eval|bench", type="md")        → quality_features[]
  Grep("../bench/{competitor}/", "security|pentest|red.?team", type="md") → security_features[]
```

---

## Step 2: Deep-Analyze Each Feature

For EACH identified competitor-only feature:

```
ACTION: Read the source file/section in local clone at ../bench/{competitor}/
EXTRACT:
  - What it does (technical description, 2-3 sentences)
  - How it's implemented (file references, key code patterns)
  - Dependencies (other features it requires)

THEN ASSESS:
  - Value for AIOX (why it matters, which workflows benefit)
  - Implementation complexity: Baixa / Media / Alta
    - Baixa: < 1 day, single file, no dependencies
    - Media: 1-3 days, 2-5 files, some integration
    - Alta: > 3 days, architectural change, multiple integrations
  - Priority: P0 (critical) / P1 (high) / P2 (medium) / P3 (low)
    - P0: Blocks competitive parity, users actively requesting
    - P1: Significant value, clear ROI
    - P2: Nice-to-have, moderate value
    - P3: Aspirational, low urgency
```

---

## Step 3: Write Feature Analysis Document

For each feature, use this structure:

```markdown
## {N}. {Feature Category}: {Feature Name}

### {N}.1 {Sub-feature Name}

**O que e:**
{Technical description from competitor source}

**Codigo/config de referencia:** `{competitor file path}`

```{language}
{Key code snippet or config example from competitor, max 20 lines}
```

**Armazenamento/Output:** `{where results are stored}`

**Valor para AIOX:**
- {Benefit 1}
- {Benefit 2}
- {Benefit 3}

**Complexidade:** {Baixa | Media | Alta}
- {Implementation notes}

**Prioridade:** {P0 | P1 | P2 | P3}
- {Justification}
```

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-features-para-aiox.md`

Structure:
1. Sumario Executivo (4-5 categories with headline assessment)
2. Feature-by-feature deep analysis
3. Summary table

---

## Step 4: Build Prioritized Roadmap

Sort features into implementation phases:

```markdown
# Roadmap: {Competitor} Features para AIOX

## Sumario

| Fase | Features | Complexidade | Valor |
|------|----------|-------------|-------|
| Quick Wins | {count} | Baixa | Alto |
| Core | {count} | Media | Alto |
| Advanced | {count} | Alta | Alto |
| Future | {count} | Variada | Medio-Baixo |

## Fase 1: Quick Wins (Baixa complexidade, Alto valor)

### 1.1 {Feature Name}
- **O que:** {1-line description}
- **Onde implementar:** {AIOX file/module}
- **Estimativa:** {Baixa}
- **Dependencias:** {none or list}
- **Criterio de pronto:** {measurable}

{repeat for each}

## Fase 2: Core Improvements (Media complexidade, Alto valor)
{same structure}

## Fase 3: Advanced Capabilities (Alta complexidade)
{same structure}

## Fase 4: Future / Nice-to-have
{same structure}

## Dependencias entre fases
{dependency graph if any}

## Metricas de sucesso
- {KPI 1}
- {KPI 2}
```

**OUTPUT:** Write `docs/bench/{competitor}/roadmap-{competitor}-features-para-aiox.md`

---

## Step 5: Generate Executable Backlog

```json
{
  "generatedAt": "<ISO-8601>",
  "competitor": "{competitor}",
  "total_items": <number>,
  "by_priority": { "P0": <n>, "P1": <n>, "P2": <n>, "P3": <n> },
  "by_complexity": { "LOW": <n>, "MEDIUM": <n>, "HIGH": <n> },
  "items": [
    {
      "id": "GAP-001",
      "title": "Implement {feature name}",
      "description": "{what and why}",
      "category": "{hooks|extensibility|learning|ux|quality|security|governance}",
      "priority": "P0",
      "complexity": "MEDIUM",
      "phase": 1,
      "source_reference": "{competitor file path}",
      "aiox_target": "{where to implement in AIOX}",
      "dependencies": [],
      "acceptance_criteria": [
        "{measurable criterion 1}",
        "{measurable criterion 2}"
      ],
      "status": "backlog"
    }
  ]
}
```

**OUTPUT (JSON):** Write `docs/bench/{competitor}/aiox-gap-closure-backlog-executable.json`

**OUTPUT (MD):** Write `docs/bench/{competitor}/aiox-gap-closure-backlog-executable.md`

MD version has same data as table:

```markdown
# Gap Closure Backlog - {Competitor}

| ID | Titulo | Prioridade | Complexidade | Fase | Categoria |
|----|--------|-----------|-------------|------|-----------|
| GAP-001 | {title} | P0 | MEDIUM | 1 | hooks |

## Detalhes

### GAP-001: {title}
{description}
**Target:** {aiox_target}
**Criterios:** {acceptance_criteria}
```

---

## Outputs

| # | File | Format |
|---|------|--------|
| 1 | `{competitor}-features-para-aiox.md` | MD |
| 2 | `roadmap-{competitor}-features-para-aiox.md` | MD |
| 3 | `aiox-gap-closure-backlog-executable.json` | JSON |
| 4 | `aiox-gap-closure-backlog-executable.md` | MD |

## Verification

- [ ] Every competitor-only feature analyzed
- [ ] Every feature has value + complexity + priority
- [ ] Code references cite real files (not invented)
- [ ] Roadmap phases are actionable
- [ ] Backlog items have acceptance criteria
- [ ] JSON is valid and parseable
- [ ] No features duplicated across phases
