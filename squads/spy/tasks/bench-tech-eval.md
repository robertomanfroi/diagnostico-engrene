# Task: Technology Evaluation

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

## Metadata
```yaml
id: bench-tech-eval
name: "Technology Evaluation"
category: benchmark-technology
agent: bench-analyst
elicit: true
autonomous: false
estimated_duration: "10-15min"
description: "Evaluate technology: maturity, ecosystem, performance, DX, community for comparison"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Evaluate a technology, framework, or programming tool by collecting maturity data,
ecosystem metrics, performance benchmarks, developer experience indicators, and
community statistics. Produces a structured inventory JSON used as input for the
universal comparison pipeline.

This task is the **technology-specific** implementation of the inventory phase.
Inspired by ThoughtWorks Technology Radar methodology.

## Prerequisites

- [ ] Technology identified (name, type)
- [ ] Comparison type confirmed as `technology`
- [ ] Internet access available for web research

## Inputs

```yaml
inputs:
  subject_name:
    type: string
    required: true
    description: "Technology identifier (e.g., 'react', 'postgresql', 'rust', 'kubernetes')"

  tech_type:
    type: enum
    values: [language, framework, database, tool, platform, library]
    required: false
    description: "Technology category"

  github_repo:
    type: string
    required: false
    description: "GitHub repository URL (for deeper analysis)"

  output_dir:
    type: string
    required: false
    description: "Override output directory"
```

## Data Collection Protocol

```
PROTOCOL: DOCS_AND_ECOSYSTEM_FIRST
METHODS: WebSearch, WebFetch, optional git clone
NEVER: Compare without version context, ignore breaking changes
ALWAYS: Cite source, note version/date for all metrics
```

---

## Step 1: Identify Technology

```
ACTION: WebSearch("{subject_name} official documentation about")
ACTION: WebFetch(official_docs_url) if found
EXTRACT:
  - Full name and current stable version
  - Type (language, framework, database, tool, platform, library)
  - License (MIT, Apache 2.0, GPL, proprietary, etc.)
  - Creator / maintaining organization
  - First release date
  - Language / platform (what it's written in or runs on)

STORE: identity = {
  name: "<full name>",
  version: "<current stable>",
  type: "<category>",
  license: "<license>",
  creator: "<org or person>",
  first_release: "<date>",
  language: "<implementation language>",
  platform: "<runtime platform>",
  url: "<official URL>"
}
```

---

## Step 2: Collect Maturity Data

```
ACTION: WebSearch("{subject_name} version history stability breaking changes")
ACTION: WebSearch("{subject_name} GitHub releases")
EXTRACT:
  - Age (years since first release)
  - Current major version
  - Version history (major milestones)
  - Breaking changes frequency
  - LTS (Long Term Support) policy
  - Deprecation policy
  - Stability reputation

STORE: maturity = {
  age_years: <number>,
  major_version: <number>,
  total_releases: <number or "unknown">,
  breaking_changes_frequency: "<rare|occasional|frequent>",
  lts_policy: "<description or 'none'>",
  deprecation_policy: "<description or 'none'>",
  stability: "<very-stable|stable|evolving|experimental>",
  milestones: [
    {version: "<X.0>", date: "<date>", significance: "<description>"}
  ],
  source: "<URL>"
}
```

---

## Step 3: Collect Ecosystem Data

```
ACTION: WebSearch("{subject_name} ecosystem packages plugins libraries")
ACTION: WebSearch("{subject_name} npm downloads" OR "{subject_name} PyPI downloads" OR "{subject_name} crates.io")
EXTRACT:
  - Package count (npm, PyPI, crates.io, etc.)
  - Key libraries / must-have packages
  - Official tooling (CLI, IDE plugins, formatters, linters)
  - Build tools compatibility
  - Framework ecosystem (if applicable)

STORE: ecosystem = {
  package_registry: "<npm|PyPI|crates.io|etc>",
  package_count: <number or "unknown">,
  key_libraries: [
    {name: "<lib>", purpose: "<what it does>", stars: <number>}
  ],
  official_tools: {
    cli: <boolean>,
    formatter: "<name or 'none'>",
    linter: "<name or 'none'>",
    ide_plugins: ["<VS Code>", "<IntelliJ>"]
  },
  build_tools: ["<tool1>", "<tool2>"],
  source: "<URL>"
}
```

---

## Step 4: Collect Performance Data

```
ACTION: WebSearch("{subject_name} benchmarks performance comparison")
EXTRACT:
  - Official benchmarks (if any)
  - Third-party benchmark results
  - Resource usage (memory, CPU)
  - Scalability characteristics
  - Known performance limitations

STORE: performance = {
  official_benchmarks: [
    {name: "<benchmark>", score: "<result>", source: "<URL>"}
  ],
  third_party_benchmarks: [
    {name: "<benchmark>", score: "<result>", source: "<URL>"}
  ],
  resource_usage: "<description>",
  scalability: "<description>",
  limitations: ["<limitation>"],
  source: "<URL>"
}
```

---

## Step 5: Collect Developer Experience (DX)

```
ACTION: WebSearch("{subject_name} developer experience documentation quality")
ACTION: WebSearch("{subject_name} error messages debugging")
EXTRACT:
  - Documentation quality and completeness
  - Getting started / tutorial quality
  - Error messages quality
  - Debugging experience
  - IDE support (autocomplete, type checking, refactoring)
  - CLI experience (if applicable)
  - Migration guides quality

STORE: developer_experience = {
  docs: {
    quality: "<excellent|good|average|poor>",
    getting_started: "<excellent|good|average|poor>",
    api_reference: "<comprehensive|partial|minimal>",
    examples: "<abundant|adequate|sparse>"
  },
  error_messages: "<helpful|adequate|cryptic>",
  debugging: "<excellent|good|average|poor>",
  ide_support: {
    vscode: "<excellent|good|average|poor>",
    intellij: "<excellent|good|average|poor>",
    type_checking: <boolean>
  },
  cli: {
    available: <boolean>,
    quality: "<excellent|good|average|poor>"
  },
  learning_curve: "<low|moderate|steep>",
  source: "<URL>"
}
```

---

## Step 6: Collect Community Data

```
ACTION: WebSearch("{subject_name} GitHub stars contributors community")
ACTION: WebSearch("{subject_name} Stack Overflow questions Discord Slack")
EXTRACT:
  - GitHub stars
  - GitHub contributors count
  - GitHub open issues / PRs
  - GitHub last commit date
  - Stack Overflow tag count / questions
  - Discord/Slack community size
  - Reddit community size
  - Conference presence

STORE: community = {
  github: {
    stars: <number>,
    contributors: <number>,
    open_issues: <number>,
    open_prs: <number>,
    last_commit: "<date>",
    repo_url: "<URL>"
  },
  stackoverflow: {
    tag: "<tag name>",
    question_count: <number or "unknown">
  },
  chat: {
    platform: "<Discord|Slack|none>",
    member_count: <number or "unknown">
  },
  reddit: {
    subreddit: "<name or 'none'>",
    members: <number or "N/A">
  },
  conferences: ["<event>"],
  source: ["<URL1>", "<URL2>"]
}
```

---

## Step 7: Collect Adoption Data

```
ACTION: WebSearch("{subject_name} adoption usage production companies using")
ACTION: WebSearch("{subject_name} job postings demand 2025 2026")
EXTRACT:
  - Package downloads (monthly)
  - Notable production users
  - Job postings mentioning the technology
  - State of JS/Python/etc. survey results (if applicable)
  - Technology Radar classification (if listed)

STORE: adoption = {
  downloads: {
    monthly: <number or "unknown">,
    registry: "<npm|PyPI|etc>",
    source: "<URL>"
  },
  notable_users: ["<company1>", "<company2>"],
  job_market: {
    demand: "<high|moderate|low|niche>",
    estimated_postings: "<description>"
  },
  survey_results: {
    name: "<State of JS|etc>",
    satisfaction: "<percentage or 'N/A'>",
    usage: "<percentage or 'N/A'>",
    source: "<URL>"
  },
  tech_radar: {
    ring: "<Adopt|Trial|Assess|Hold|not listed>",
    source: "<URL or 'not listed'>"
  }
}
```

---

## Step 8: GitHub Deep Dive (Optional)

```
IF github_repo provided:
  ACTION: WebFetch("{github_repo}")
  EXTRACT:
    - Release frequency (releases per year)
    - Average issue resolution time
    - PR merge time
    - Code of conduct
    - Contributing guide quality
    - CI/CD setup
    - Test coverage (if visible)

  STORE: github_deep = {
    release_frequency: "<per year>",
    issue_resolution: "<fast|moderate|slow>",
    pr_merge_time: "<fast|moderate|slow>",
    code_of_conduct: <boolean>,
    contributing_guide: <boolean>,
    ci_cd: "<provider>",
    source: "<URL>"
  }
```

---

## Step 9: Compile Inventory

```json
{
  "subject": "{subject_name}",
  "type": "technology",
  "generatedAt": "<ISO-8601>",
  "method": "web-research-docs-and-ecosystem",
  "identity": {},
  "maturity": {},
  "ecosystem": {},
  "performance": {},
  "developer_experience": {},
  "community": {},
  "adoption": {},
  "github_deep": {},
  "sources_consulted": [],
  "data_quality": {
    "ecosystem_data": "<current|possibly-outdated>",
    "community_stats": "<live|cached>",
    "benchmarks": "<official|third-party|unavailable>",
    "confidence": "<high|medium|low>"
  }
}
```

---

## Step 10: Write Outputs

```
ACTION: Write("{output_dir}/inventory-{subject_name}.json", JSON.stringify(inventory, null, 2))
ACTION: Write("{output_dir}/inventory-{subject_name}.md", markdown_summary)
```

The markdown summary should include:
- Technology identity card
- Key metrics table (stars, downloads, age, version)
- Ecosystem overview
- DX assessment
- Community health indicators
- Adoption signals
- ThoughtWorks Radar classification (if available)

---

## Outputs

| File | Location | Format |
|------|----------|--------|
| Technology inventory | `{output_dir}/inventory-{subject_name}.json` | JSON |
| Technology summary | `{output_dir}/inventory-{subject_name}.md` | MD |

## Veto Conditions

1. **Technology not identifiable** — Cannot find official docs or repo → HALT
2. **Ambiguous name** — Multiple technologies with same name → ask user to clarify
3. **No public data** — Proprietary technology with no public info → WARN and collect what's available

## Verification

- [ ] JSON inventory file is valid (parseable)
- [ ] GitHub stats are current (check last commit date)
- [ ] Downloads/stats have source URLs
- [ ] Version information is current
- [ ] No fabricated metrics
- [ ] Sources consulted list is complete
- [ ] Data quality assessment is honest
