# Task: Deep Component-by-Component Comparison (Autonomous)

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
| **Task ID** | `bench-deep-compare` |
| **Version** | `1.0.0` |
| **Status** | `pending` |
| **Responsible Executor** | `bench-analyst` |
| **Execution Type** | `Agent` |
| **Model** | `claude-sonnet-4-20250514` |
| **Haiku Eligible** | `false` |
| **Estimated Duration** | `25-40min` |

## Metadata
```yaml
id: bench-deep-compare
name: "Deep Component-by-Component Comparison"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "25-40min"
description: "Side-by-side deep analysis of every structural dimension between AIOX and competitor with actual code/config blocks"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Produce an exhaustive, component-by-component deep comparison between AIOX and a
competitor framework. Unlike the quick comparison (matrices and counts), this task
extracts **actual code blocks, YAML configs, and output templates** from both frameworks
and places them side-by-side for direct analysis.

This is the task that produced the PAI 779-line deep analysis document.

## Input

| Input | Type | Required | Source |
|-------|------|----------|--------|
| `competitor_name` | string | YES | Elicited or pipeline param |
| `competitor_source_path` | string | YES | Local clone path or docs URL |
| `aiox_root` | string | YES | Auto-detected (`.aiox-core/`) |
| `comparison_data` | object | NO | Output from `bench-quick-compare` (matrices) |
| `agent_command_inventory` | JSON | NO | `docs/bench/{competitor}/appendix-aiox-agent-command-inventory.json` |

## Output

| Output | Format | Destination |
|--------|--------|-------------|
| Deep comparison report | Markdown | `docs/bench/{competitor}/{competitor}-vs-aiox-comparacao-profunda.md` |
| Agent personas comparison | Markdown | `docs/bench/{competitor}/{competitor}-vs-aiox-agent-personas-comparacao.md` |

## Prerequisites

- [ ] Competitor repo cloned locally at `../bench/{competitor}/`
- [ ] AIOX agent definitions accessible at `.aiox-core/development/agents/`
- [ ] At least a quick comparison exists (recommended but not blocking)

## Reference

See `docs/bench/pai/pai-vs-aiox-comparacao-profunda.md` for the canonical output format (779 lines).

---

## CRITICAL: Local Clone Rule

**Every benchmark MUST work from a locally cloned repository.**

```
IF ../bench/{competitor}/ does NOT exist AND repo_url is available:
  ACTION: Bash("git clone {repo_url} ../bench/{competitor}")

IF ../bench/{competitor}/ exists:
  ACTION: Bash("ls ../bench/{competitor}/") to verify
  STORE: competitor_root = ../bench/{competitor}/

ELSE:
  HALT: "Cannot run deep comparison without local clone."

All subsequent steps use Glob/Read on competitor_root (../bench/{competitor}/).
NEVER use WebFetch for competitor structural data.
NEVER estimate. NEVER invent file contents.
```

---

## Veto Conditions

The task MUST NOT execute (or must HALT immediately) if:

1. **No competitor source available** -- Cannot produce side-by-side code blocks without actual competitor source files. A docs-only summary is NOT a deep comparison.
2. **Competitor has fewer than 2 agent definitions** -- If the framework is too minimal to warrant deep analysis, use `bench-quick-compare` instead.
3. **AIOX agent files not found** -- If `.aiox-core/development/agents/` is empty or missing, the AIOX side of the comparison cannot be populated. Run `bench-inventory` first.
4. **Output file already exists and is less than 48h old** -- Do not overwrite a recent deep analysis unless explicitly requested with `--force`.

---

## Autonomous Execution Protocol

This task runs WITHOUT user interaction. Execute all steps sequentially,
extract real code/config from both frameworks, generate side-by-side analysis,
and write output files. Report completion with summary statistics.

**CRITICAL RULES:**
- Every claim MUST be backed by actual code/config extracted from source files
- NO invented examples -- if a feature does not exist, state "Not implemented"
- Winner analysis per aspect must cite the specific advantage
- All YAML/code blocks must be verbatim extracts, not paraphrased
- PT-BR for analysis text, English for code/config blocks (matching source language)

---

## Step 1: Load AIOX Agent Definitions

```
ACTION: Glob(".aiox-core/development/agents/*.md")
STORE: aiox_agent_files[]

For EACH aiox_agent_file:
  ACTION: Read(file_path)
  EXTRACT:
    - agent.id, agent.name, agent.title
    - persona_profile (archetype, communication style, vocabulary)
    - commands[] (full list with descriptions)
    - whenToUse / tier
    - output format requirements (if any)
    - core principles / methodology
  STORE: aiox_agents[agent.id] = extracted_data
```

---

## Step 2: Load Competitor Agent Definitions

```
NOTE: competitor_root = ../bench/{competitor}/ (from clone rule above)

ACTION: Glob("../bench/{competitor}/**/agents/**") OR
        Glob("../bench/{competitor}/**/personas/**") OR
        Glob("../bench/{competitor}/**/roles/**")
STORE: comp_agent_files[]

For EACH comp_agent_file:
  ACTION: Read(file_path)
  EXTRACT:
    - Agent name, role, title
    - Persona definition (backstory, voice settings, personality)
    - Commands or capabilities
    - Output format requirements
    - Methodology or principles
    - Any unique features (voice, micro-cycles, etc.)
  STORE: comp_agents[agent_id] = extracted_data

IF comp_agent_files.length == 0:
  TRY: Grep("../bench/{competitor}/", "agent|persona|role", type="md,yaml,json")
  EXTRACT: Agent-like definitions from whatever structure exists
```

---

## Step 3: Agent Persona Deep Comparison

For EACH agent pair (competitor agent mapped to AIOX equivalent):

```
WRITE section:
  ## {N}. COMPONENT: {comp_agent_name} ({competitor}) vs {aiox_agent_name} (AIOX)

  ### {N}.1 Definicao de Persona

  **{competitor} {comp_agent_name}:**
  ```yaml
  {verbatim YAML extract from competitor agent definition}
  ```

  **AIOX {aiox_agent_name}:**
  ```yaml
  {verbatim YAML extract from AIOX agent definition}
  ```

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | {aspect_1} | {detail} | {detail} | {winner} |
  | {aspect_2} | {detail} | {detail} | {winner} |
  ...

REPEAT for every mappable agent pair.
For agents without equivalent, create a section noting:
  "Sem equivalente direto em {other_framework}"
```

---

## Step 4: Output Format Comparison

For EACH agent pair:

```
WRITE section:
  ### {N}.2 Output Format Obrigatorio

  **{competitor} {agent_name} (TODA resposta):**
  ```markdown
  {verbatim output template from competitor}
  ```

  **AIOX {agent_name}:**
  {describe AIOX output format or show template}

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | Consistencia de output | {assessment} | {assessment} | {winner} |
  | Overhead cognitivo | {assessment} | {assessment} | {winner} |
  | Parseability | {assessment} | {assessment} | {winner} |
  | Flexibilidade | {assessment} | {assessment} | {winner} |
```

---

## Step 5: Development Methodology Comparison

```
ACTION: Extract core development methodology from competitor:
  Grep("{competitor_source_path}", "article|principle|rule|methodology|philosophy", type="md")
  Read relevant files

ACTION: Extract AIOX development methodology:
  Read(".claude/rules/workflow-execution.md")
  Read(".claude/rules/story-lifecycle.md")
  Read AIOX dev agent definition

WRITE section:
  ### {N}.3 Metodologia de Desenvolvimento

  **{competitor} - {methodology_name}:**
  ```markdown
  {verbatim principles/articles from competitor}
  ```

  **AIOX dev - Core Principles:**
  ```markdown
  {verbatim principles from AIOX}
  ```

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | Filosofia de arquitetura | {detail} | {detail} | {winner} |
  | TDD enforcement | {detail} | {detail} | {winner} |
  | Scope discipline | {detail} | {detail} | {winner} |
  | Code review | {detail} | {detail} | {winner} |
  | Pragmatismo | {detail} | {detail} | {winner} |
```

---

## Step 6: Command Surface Comparison

For EACH agent pair with commands:

```
WRITE section:
  ### {N}.4 Superficie de Comandos

  **{competitor} {agent_name} commands:**
  | Comando | Descricao | Equivalente AIOX |
  |---------|-----------|------------------|
  {for each competitor command}

  **AIOX {agent_name} commands:**
  | Comando | Descricao | Equivalente {competitor} |
  |---------|-----------|--------------------------|
  {for each AIOX command}

  **Delta:**
  - Comandos exclusivos {competitor}: {count} ({list})
  - Comandos exclusivos AIOX: {count} ({list})
  - Cobertura mutua: {percentage}%
```

---

## Step 7: Quality Gates Comparison

```
ACTION: Extract quality gate definitions from competitor:
  Grep("{competitor_source_path}", "quality|gate|check|validation|review", type="md,yaml")
  Read relevant files

ACTION: Extract AIOX quality gates:
  Read(".claude/rules/story-lifecycle.md") → 7 quality checks
  Read(".claude/rules/coderabbit-integration.md") → self-healing config
  Read QA agent definition

WRITE section:
  ## {N+1}. QUALITY GATES: {competitor} vs AIOX

  **{competitor} Quality System:**
  ```yaml
  {verbatim quality gate config from competitor}
  ```

  **AIOX Quality System:**
  ```yaml
  {verbatim quality gate config from AIOX}
  ```

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | Automated checks | {detail} | {detail} | {winner} |
  | Self-healing | {detail} | {detail} | {winner} |
  | Gate severity levels | {detail} | {detail} | {winner} |
  | Review iterations | {detail} | {detail} | {winner} |
  | Blocking vs advisory | {detail} | {detail} | {winner} |
```

---

## Step 8: Constitutional/Governance Comparison

```
ACTION: Extract governance model from competitor:
  Grep("{competitor_source_path}", "constitution|governance|article|law|rule|policy", type="md")
  Read relevant files

ACTION: Extract AIOX governance:
  Read(".claude/rules/agent-authority.md")
  Read(".claude/rules/ids-principles.md")
  Read relevant governance files

WRITE section:
  ## {N+2}. GOVERNANCE: {competitor} vs AIOX

  **{competitor} Governance:**
  ```markdown
  {verbatim governance rules from competitor}
  ```

  **AIOX Governance:**
  ```markdown
  {verbatim governance rules from AIOX}
  ```

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | Agent authority model | {detail} | {detail} | {winner} |
  | Decision hierarchy | {detail} | {detail} | {winner} |
  | Override mechanisms | {detail} | {detail} | {winner} |
  | Constitutional depth | {detail} | {detail} | {winner} |
  | Enforcement rigor | {detail} | {detail} | {winner} |
```

---

## Step 9: Workflow Execution Comparison

```
ACTION: Extract workflow execution model from competitor:
  Grep("{competitor_source_path}", "workflow|pipeline|phase|step|stage", type="md,yaml")
  Read relevant files

ACTION: Extract AIOX workflow model:
  Read(".claude/rules/workflow-execution.md")
  Scan ".aiox-core/development/workflows/"

WRITE section:
  ## {N+3}. WORKFLOW EXECUTION: {competitor} vs AIOX

  **{competitor} Workflow Model:**
  ```
  {verbatim workflow phases/stages from competitor}
  ```

  **AIOX Workflow Model:**
  ```
  {verbatim 4 primary workflows from AIOX}
  ```

  **Analise:**
  | Aspecto | {competitor} | AIOX | Vencedor |
  |---------|--------------|------|----------|
  | Number of workflows | {count} | {count} | {winner} |
  | Phase granularity | {detail} | {detail} | {winner} |
  | Agent handoff model | {detail} | {detail} | {winner} |
  | Decision points | {detail} | {detail} | {winner} |
  | Rollback capability | {detail} | {detail} | {winner} |
```

---

## Step 10: Unique/Exclusive Features Comparison

```
ACTION: Identify features that exist in ONLY one framework:

COMPETITOR-ONLY features:
  - Scan for patterns not present in AIOX (voice, micro-cycles, specific tooling, etc.)
  - For each, extract verbatim implementation

AIOX-ONLY features:
  - Scan for patterns not present in competitor (squads, IDS, task anatomy, etc.)
  - For each, extract verbatim implementation

WRITE section:
  ## {N+4}. FEATURES EXCLUSIVAS

  ### Features exclusivas de {competitor}
  | Feature | Descricao | Impacto | AIOX deveria absorver? |
  |---------|-----------|---------|------------------------|
  {for each exclusive feature}

  ### Features exclusivas de AIOX
  | Feature | Descricao | Impacto | Diferencial competitivo? |
  |---------|-----------|---------|--------------------------|
  {for each exclusive feature}
```

---

## Step 11: Winner Summary & Scorecard

```
WRITE section:
  ## SCORECARD FINAL

  | Dimensao | {competitor} | AIOX | Vencedor |
  |----------|--------------|------|----------|
  | Agent Personas | {score}/10 | {score}/10 | {winner} |
  | Output Format | {score}/10 | {score}/10 | {winner} |
  | Metodologia | {score}/10 | {score}/10 | {winner} |
  | Comandos | {score}/10 | {score}/10 | {winner} |
  | Quality Gates | {score}/10 | {score}/10 | {winner} |
  | Governance | {score}/10 | {score}/10 | {winner} |
  | Workflows | {score}/10 | {score}/10 | {winner} |
  | Features Exclusivas | {score}/10 | {score}/10 | {winner} |
  | **TOTAL** | **{total}/80** | **{total}/80** | **{overall_winner}** |

  ### Interpretacao
  {2-3 paragraph summary of overall findings, key strengths of each framework,
   and areas where each should learn from the other}
```

---

## Step 12: Generate Agent Personas Comparison Document

```
ACTION: Extract the agent persona sections from Step 3 into a separate dedicated file.

For EACH agent pair:
  WRITE to separate file:
    ## {comp_agent} ({competitor}) vs {aiox_agent} (AIOX)

    ### Persona Definition Side-by-Side
    {full YAML blocks from both}

    ### Communication Style
    {tone, vocabulary, greeting patterns}

    ### Capabilities Overlap
    {Venn diagram in text: shared, competitor-only, AIOX-only}

    ### Recommendation
    {What AIOX should absorb from this competitor agent persona}

OUTPUT: docs/bench/{competitor}/{competitor}-vs-aiox-agent-personas-comparacao.md
```

---

## Step 13: Write Output Files

```
ACTION: Assemble all sections from Steps 3-11 into main document
OUTPUT: docs/bench/{competitor}/{competitor}-vs-aiox-comparacao-profunda.md

HEADER of main document:
  # {competitor} vs AIOX - Comparacao Profunda Componente a Componente

  Data: {YYYY-MM-DD}
  Objetivo: Analise tecnica exaustiva com codigo, exemplos e diferencas operacionais
  Status: documento privado local (nao comitar)

ACTION: Assemble Step 12 into separate file
OUTPUT: docs/bench/{competitor}/{competitor}-vs-aiox-agent-personas-comparacao.md

REPORT completion:
  - Main document: {line_count} lines
  - Agent personas document: {line_count} lines
  - Agents compared: {count}
  - Dimensions analyzed: {count}
  - Tables generated: {count}
  - Code blocks extracted: {count}
```

---

## Acceptance Criteria

The task is complete when ALL of the following are met:

- [ ] **AC-1:** Main output file exists at `docs/bench/{competitor}/{competitor}-vs-aiox-comparacao-profunda.md`
- [ ] **AC-2:** Agent personas file exists at `docs/bench/{competitor}/{competitor}-vs-aiox-agent-personas-comparacao.md`
- [ ] **AC-3:** Main document has 400+ lines (deep analysis must be thorough)
- [ ] **AC-4:** Every comparison dimension includes actual code/YAML blocks from BOTH frameworks (no placeholders)
- [ ] **AC-5:** Every dimension has an "Analise" table with per-aspect winner assessment
- [ ] **AC-6:** Scorecard Final section exists with numeric scores per dimension
- [ ] **AC-7:** No invented examples -- all code blocks are verbatim extracts from source files
- [ ] **AC-8:** All competitor agents with an AIOX equivalent are covered
- [ ] **AC-9:** Exclusive features section documents features unique to each framework
- [ ] **AC-10:** Document follows the format pattern of `docs/bench/pai/pai-vs-aiox-comparacao-profunda.md`

## Quality Validation

After generation, validate against `bench-quality-checklist.md` (if available):

- [ ] All markdown headings follow consistent hierarchy
- [ ] All tables are valid markdown tables
- [ ] All code blocks specify language for syntax highlighting
- [ ] No broken references or placeholder text remaining
- [ ] PT-BR used consistently for analysis text
- [ ] Scoring method and confidence level disclosed

---

## Error Handling

| Error | Detection | Recovery |
|-------|-----------|----------|
| Competitor source not accessible | `Glob` returns empty | HALT with clear error message |
| AIOX agents directory empty | No `.md` files in agents dir | Run `bench-inventory` first |
| Agent mapping ambiguous | Multiple possible matches | Map to closest equivalent, note uncertainty |
| Code block extraction fails | File unreadable or binary | Skip block, note "Could not extract" |
| Output path not writable | Write fails | Report path issue, suggest alternative |

## Integration

| Task | Relationship |
|------|-------------|
| `bench-inventory` | Upstream -- provides AIOX baseline data |
| `bench-quick-compare` | Upstream (optional) -- provides matrices for context |
| `bench-absorb` | Downstream -- uses exclusive features for absorption roadmap |
| `bench-framework` | Parent orchestrator -- calls this task in Phase 6 |

---

_Task Version: 1.0.0_
_Pattern: HO-TP-001 (Task Anatomy Standard)_
_Created: 2026-02-17_
_Compliant: Yes_
