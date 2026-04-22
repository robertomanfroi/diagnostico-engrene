# Task: Benchmark Type Detection

## Contrato SINKRA

Domain: `Tactical`

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

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `bench-detect` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Agent` |
| **Estimated Duration** | `2-3min` |

## Metadata
```yaml
id: bench-detect
name: "Benchmark Type Detection"
category: benchmark-core
agent: bench-analyst
elicit: true
estimated_duration: "2-3min"
description: "Auto-detect comparison type based on subject names/URLs, load matching dimensions and data source strategy"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Auto-detect the comparison type for a benchmark based on subject names, URLs, or identifiers.
Outputs the comparison type, matching dimension pack, and data source acquisition strategy.
This task is the **entry point** for all universal benchmarks — it determines how
subsequent phases (inventory, matrix, score) will behave.

## Autonomous Execution Protocol

This task runs with MINIMAL user interaction. Auto-detection runs first, then
the user is asked to confirm or override the detected type.

---

## Prerequisites

- [ ] At least two subjects provided (subject_a and subject_b)
- [ ] `bench-dimension-packs.yaml` accessible in `squads/spy/data/`
- [ ] `bench-data-sources.yaml` accessible in `squads/spy/data/`

## Inputs

```yaml
inputs:
  subject_a:
    type: string
    required: true
    description: "First subject — name, URL, or local path"
    elicit: true
    prompt: "Subject A (name, URL, or path):"

  subject_b:
    type: string
    required: true
    description: "Second subject — name, URL, or local path"
    elicit: true
    prompt: "Subject B (name, URL, or path):"

  force_type:
    type: enum
    required: false
    values: [codebase, llm, product, company, technology]
    description: "Override auto-detection with explicit type"
    elicit: false
```

---

## Step 1: Validate Subjects

```
ACTION: Compare subject_a and subject_b
CHECK: subject_a != subject_b (case-insensitive, normalized)
STORE: subject_a_normalized, subject_b_normalized
```

**VETO:** If both subjects resolve to the same entity after normalization → HALT.
Display: "Cannot compare a subject against itself. Provide two distinct subjects."

---

## Step 2: Check Force Override

```
IF force_type is provided AND force_type in [codebase, llm, product, company, technology]:
  STORE: detected_type = force_type
  STORE: detection_method = "user_override"
  SKIP to Step 4
```

---

## Step 3: Pattern-Based Detection

Run detection rules in priority order. First match wins.

### 3.1: GitHub URL or Local Path → codebase

```
ACTION: Check subject_a and subject_b against patterns:
  - Regex: ^https?://github\.com/[\w-]+/[\w-]+
  - Regex: ^git@github\.com:[\w-]+/[\w-]+
  - Regex: ^(/|\.\.?/|~/) (local filesystem path)
  - Contains: .git, package.json, Cargo.toml, go.mod, pyproject.toml
MATCH: Both subjects match → codebase
STORE: detection_confidence = "high"
```

### 3.2: Known LLM Names → llm

```
ACTION: Check subject_a and subject_b against known LLM identifiers:
  - Exact: gpt-4, gpt-4o, gpt-4-turbo, gpt-3.5-turbo, o1, o1-mini, o1-pro, o3, o3-mini
  - Exact: claude-3-opus, claude-3-sonnet, claude-3-haiku, claude-3.5-sonnet, claude-4-opus
  - Exact: gemini-pro, gemini-ultra, gemini-1.5-pro, gemini-1.5-flash, gemini-2.0
  - Exact: llama-2, llama-3, llama-3.1, llama-3.2, codellama, mixtral, mistral
  - Exact: command-r, command-r-plus, deepseek-v3, deepseek-r1, qwen-2.5, phi-4
  - Pattern: contains "gpt", "claude", "gemini", "llama", "mistral", "deepseek"
MATCH: Both subjects match → llm
STORE: detection_confidence = "high"
```

### 3.3: Known Product Patterns → product

```
ACTION: Check subject_a and subject_b against:
  - Known SaaS names: slack, notion, linear, jira, asana, figma, vercel, netlify, etc.
  - Pattern: ends with ".com", ".io", ".app", ".dev" (product website URLs)
  - Pattern: contains "pricing", "plans", "features" in URL
MATCH: Both subjects match → product
STORE: detection_confidence = "medium"
```

### 3.4: Known Company Indicators → company

```
ACTION: Check subject_a and subject_b against:
  - Suffixes: Inc, Corp, Ltd, GmbH, LLC, Co.
  - Known companies: Google, Microsoft, Apple, Meta, Amazon, OpenAI, Anthropic, etc.
  - Pattern: Crunchbase URL, LinkedIn company URL
MATCH: Both subjects match → company
STORE: detection_confidence = "medium"
```

### 3.5: Known Technology Names → technology

```
ACTION: Check subject_a and subject_b against:
  - Frameworks: react, angular, vue, svelte, next.js, nuxt, remix, astro
  - Languages: python, typescript, rust, go, java, kotlin, swift
  - Databases: postgres, mysql, mongodb, redis, supabase, firebase
  - Tools: docker, kubernetes, terraform, webpack, vite, esbuild
  - Runtimes: node, deno, bun
MATCH: Both subjects match → technology
STORE: detection_confidence = "medium"
```

### 3.6: Ambiguous → Ask User

```
IF no pattern matched:
  ACTION: Present user with options
  PROMPT: |
    Could not auto-detect comparison type for:
    - Subject A: {subject_a}
    - Subject B: {subject_b}

    Select type:
    1. codebase  — Source code repository comparison
    2. llm       — Large Language Model comparison
    3. product   — Software product comparison
    4. company   — Company competitive analysis
    5. technology — Technology/framework comparison

  STORE: detected_type = user_selection
  STORE: detection_method = "user_selected"
  STORE: detection_confidence = "high"
```

---

## Step 4: Load Dimension Pack

```
ACTION: Read("squads/spy/data/bench-dimension-packs.yaml")
EXTRACT: types.{detected_type}.dimensions[]
STORE: dimensions[] = extracted dimensions array
STORE: dimension_count = dimensions.length
```

FAIL_CONDITION: No dimensions found for detected_type → HALT with error.

---

## Step 5: Load Data Source Strategy

```
ACTION: Read("squads/spy/data/bench-data-sources.yaml")
EXTRACT: types.{detected_type}
STORE: data_source_config = {
  primary: types.{detected_type}.primary,
  protocol: types.{detected_type}.protocol,
  methods: types.{detected_type}.methods,
  sources: types.{detected_type}.sources,
  never: types.{detected_type}.never
}
```

FAIL_CONDITION: No data source config for detected_type → HALT with error.

---

## Step 6: Compute Output Directory

```
ACTION: Normalize subject names for filesystem use
  - Lowercase
  - Replace spaces with hyphens
  - Remove special characters except hyphens and dots
  - Truncate to 40 chars per subject

STORE: subject_a_slug = normalize(subject_a)
STORE: subject_b_slug = normalize(subject_b)
STORE: output_dir = "docs/bench/{subject_a_slug}-vs-{subject_b_slug}/"
```

---

## Step 7: Confirm with User (elicit: true)

```
ACTION: Present detection summary for confirmation
DISPLAY:
  ---
  Benchmark Type Detection Summary
  ---
  Subject A: {subject_a}
  Subject B: {subject_b}
  Detected Type: {detected_type}
  Detection Method: {detection_method}
  Confidence: {detection_confidence}

  Dimensions ({dimension_count}):
  {for each dimension: "  - {name} (weight: {weight})"}

  Data Strategy: {data_source_config.protocol}
  Methods: {data_source_config.methods}
  Sources: {data_source_config.sources}

  Output Directory: {output_dir}
  ---

PROMPT: "Confirm? (Y to proceed / N to change type / type name to override)"

IF user confirms:
  PROCEED to Step 8

IF user provides type override:
  STORE: detected_type = user_override
  STORE: detection_method = "user_corrected"
  GOTO Step 4 (reload dimension pack)
```

---

## Step 8: Compile Detection Output

```
STORE: detection_result = {
  "subject_a": subject_a,
  "subject_b": subject_b,
  "subject_a_slug": subject_a_slug,
  "subject_b_slug": subject_b_slug,
  "comparison_type": detected_type,
  "detection_method": detection_method,
  "detection_confidence": detection_confidence,
  "dimensions": dimensions[],
  "data_source_config": data_source_config,
  "output_dir": output_dir,
  "detected_at": "<ISO-8601>"
}
```

This result is passed directly to subsequent pipeline phases (bench-inventory,
bench-matrix, bench-score, etc.) via in-memory context. No file write is
required unless the full pipeline is being executed, in which case it is
persisted as part of the pipeline state.

---

## Outputs

| Output | Type | Destination |
|--------|------|-------------|
| `detection_result` | In-memory object | Passed to next pipeline phase |
| Type confirmation | User interaction | Displayed in console |

Optional persistence (when running full pipeline):

| File | Location | Format |
|------|----------|--------|
| `bench-detection.json` | `{output_dir}/bench-detection.json` | JSON |

---

## Veto Conditions

The task MUST HALT if:

1. **Identical subjects** — `subject_a` and `subject_b` resolve to the same entity after normalization. Cannot compare something against itself.
2. **Neither subject identifiable** — Both subjects fail all pattern matching AND user declines to select a type manually.
3. **Dimension pack missing** — `bench-dimension-packs.yaml` not found or does not contain dimensions for the detected type.
4. **Data sources missing** — `bench-data-sources.yaml` not found or does not contain config for the detected type.
5. **Invalid force_type** — `force_type` provided but not one of the 5 valid types.

---

## Verification

- [ ] Type is one of: `codebase`, `llm`, `product`, `company`, `technology`
- [ ] Dimensions loaded correctly for detected type (count > 0)
- [ ] Dimension weights sum to 1.0 (within 0.01 tolerance)
- [ ] Data source strategy matches detected type
- [ ] Output directory path is valid and normalized
- [ ] Subject slugs contain no invalid filesystem characters
- [ ] Detection method is recorded (`auto`, `user_override`, `user_selected`, `user_corrected`)
- [ ] Detection confidence is recorded (`high`, `medium`, `low`)
