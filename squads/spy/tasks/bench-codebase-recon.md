# Task: Codebase Reconnaissance

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
id: bench-codebase-recon
name: "Codebase Reconnaissance"
category: benchmark-codebase
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "8-12min"
description: "Git clone + filesystem scan for codebase comparison. Produces structured inventory of a source code repository."
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Perform deep reconnaissance of a source code repository. Clone locally (if remote),
scan the filesystem, detect languages/frameworks/patterns, count artifacts, and produce
a structured inventory JSON used as input for universal comparison pipeline.

This task is the **codebase-specific** implementation of the inventory phase.
It replaces the recon portions of the old `bench-framework.md` Phase 2.

## Prerequisites

- [ ] Subject identified (name + source URL or local path)
- [ ] Comparison type confirmed as `codebase`
- [ ] Write access to `../bench/` directory for cloning

## Inputs

```yaml
inputs:
  subject_name:
    type: string
    required: true
    description: "Subject identifier slug (e.g., 'react', 'nextjs', 'bmad')"

  source:
    type: string
    required: true
    description: "GitHub URL or local filesystem path"

  source_type:
    type: enum
    values: [repo_local, repo_github]
    default: repo_github
    description: "How to access the codebase"

  output_dir:
    type: string
    required: false
    description: "Override output directory (default: docs/bench/{context}/)"
```

## CRITICAL: Clone Protocol

```
STEP 0: Ensure local clone exists

IF source_type = repo_github AND ../bench/{subject_name}/ does NOT exist:
  ACTION: Bash("git clone {source} ../bench/{subject_name}")
  STORE: subject_root = ../bench/{subject_name}/

IF source_type = repo_local AND {source} is provided:
  ACTION: Bash("ls {source}") to verify exists
  STORE: subject_root = {source}

IF ../bench/{subject_name}/ already exists:
  ACTION: Bash("ls ../bench/{subject_name}/") to verify
  STORE: subject_root = ../bench/{subject_name}/

ELSE:
  HALT: "Cannot analyze codebase without local files. Provide source URL or path."
```

**Rules:**
- ALL Glob/Read/Grep operations target `subject_root`
- NEVER use WebFetch for structural data
- NEVER estimate counts — count real files from local clone
- NEVER invent file paths or content
- Clone goes OUTSIDE the project directory (`../bench/`)

---

## Step 1: Discover Structure

```
ACTION: Bash("find {subject_root} -type f -name '*.md' -o -name '*.yaml' -o -name '*.yml' -o -name '*.ts' -o -name '*.js' -o -name '*.py' -o -name '*.go' -o -name '*.rs' | head -500")
ACTION: Bash("ls -la {subject_root}/")
IDENTIFY: Top-level directory structure
STORE: dir_structure
```

---

## Step 2: Detect Languages & Frameworks

```
ACTION: Glob("{subject_root}/package.json") → Node.js/JavaScript
ACTION: Glob("{subject_root}/pyproject.toml") OR Glob("{subject_root}/setup.py") → Python
ACTION: Glob("{subject_root}/go.mod") → Go
ACTION: Glob("{subject_root}/Cargo.toml") → Rust
ACTION: Glob("{subject_root}/*.sln") OR Glob("{subject_root}/*.csproj") → .NET
ACTION: Glob("{subject_root}/pom.xml") OR Glob("{subject_root}/build.gradle") → Java/Kotlin

IF package.json exists:
  ACTION: Read("{subject_root}/package.json", limit=50)
  EXTRACT: dependencies, devDependencies, scripts
  IDENTIFY: Frameworks (react, vue, angular, next, express, etc.)

STORE: languages[], frameworks[], package_manager
```

---

## Step 3: Scan Agent/Workflow Definitions (if AI framework)

```
ACTION: Glob("{subject_root}/**/agents/*.md") OR Glob("{subject_root}/**/agents/*.yaml")
ACTION: Glob("{subject_root}/**/workflows/*.yaml") OR Glob("{subject_root}/**/workflows/*.md")
ACTION: Glob("{subject_root}/**/tasks/*.md") OR Glob("{subject_root}/**/tasks/*.yaml")
ACTION: Glob("{subject_root}/**/skills/*/SKILL.md")

For EACH agent file found:
  ACTION: Read(file, limit=60)
  EXTRACT: name, role, commands (if any)

STORE: agents[], workflows[], tasks[], skills[]
```

---

## Step 4: Count Files by Type

```
ACTION: Bash("find {subject_root} -type f -name '*.ts' | wc -l") → ts_count
ACTION: Bash("find {subject_root} -type f -name '*.js' | wc -l") → js_count
ACTION: Bash("find {subject_root} -type f -name '*.py' | wc -l") → py_count
ACTION: Bash("find {subject_root} -type f -name '*.md' | wc -l") → md_count
ACTION: Bash("find {subject_root} -type f -name '*.yaml' -o -name '*.yml' | wc -l") → yaml_count
ACTION: Bash("find {subject_root} -type f -name '*.json' | wc -l") → json_count
ACTION: Bash("find {subject_root} -type f | wc -l") → total_files
ACTION: Bash("find {subject_root} -type d | wc -l") → total_dirs

STORE: file_counts{}
```

---

## Step 5: Estimate LOC

```
ACTION: Bash("find {subject_root} -type f \( -name '*.ts' -o -name '*.js' -o -name '*.py' -o -name '*.go' -o -name '*.rs' \) -exec cat {} + | wc -l") → code_loc
ACTION: Bash("find {subject_root} -type f -name '*.md' -exec cat {} + | wc -l") → docs_loc

STORE: loc = {code: code_loc, docs: docs_loc, total: code_loc + docs_loc}
```

---

## Step 6: Detect Testing Setup

```
ACTION: Glob("{subject_root}/**/test/**") OR Glob("{subject_root}/**/__tests__/**") OR Glob("{subject_root}/**/*.test.*") OR Glob("{subject_root}/**/*.spec.*")
ACTION: Glob("{subject_root}/jest.config.*") OR Glob("{subject_root}/vitest.config.*") OR Glob("{subject_root}/pytest.ini") OR Glob("{subject_root}/conftest.py")
ACTION: Glob("{subject_root}/.github/workflows/*.yml") → CI config
ACTION: Grep("{subject_root}", "coverage") → coverage config references

STORE: testing = {
  test_files_count: <number>,
  test_framework: "<detected>",
  coverage_config: <boolean>,
  ci_config: <boolean>,
  ci_provider: "<github|gitlab|circleci|etc>"
}
```

---

## Step 7: Detect Documentation Quality

```
ACTION: Read("{subject_root}/README.md", limit=50) → README exists and quality
ACTION: Glob("{subject_root}/docs/**/*.md") → docs count
ACTION: Glob("{subject_root}/**/API.md") OR Glob("{subject_root}/**/api/**") → API docs
ACTION: Grep("{subject_root}", "JSDoc|docstring|///") → inline docs presence

STORE: documentation = {
  readme_exists: <boolean>,
  readme_lines: <number>,
  docs_files: <number>,
  api_docs: <boolean>,
  inline_docs: <boolean>
}
```

---

## Step 8: Detect Automation & Tooling

```
ACTION: Glob("{subject_root}/.github/workflows/*.yml") → GitHub Actions
ACTION: Glob("{subject_root}/.gitlab-ci.yml") → GitLab CI
ACTION: Glob("{subject_root}/Makefile") OR Glob("{subject_root}/Taskfile.yml") → Build automation
ACTION: Glob("{subject_root}/.eslintrc*") OR Glob("{subject_root}/biome.json") → Linting
ACTION: Glob("{subject_root}/tsconfig.json") → TypeScript config
ACTION: Glob("{subject_root}/.husky/**") OR Glob("{subject_root}/.git/hooks/*") → Git hooks
ACTION: Glob("{subject_root}/Dockerfile") OR Glob("{subject_root}/docker-compose*") → Docker

STORE: automation = {
  ci_cd: "<provider>",
  linting: <boolean>,
  type_checking: <boolean>,
  git_hooks: <boolean>,
  containerization: <boolean>,
  build_scripts: []
}
```

---

## Step 9: Detect Architecture Patterns

```
ACTION: Bash("ls -d {subject_root}/*/") → top-level folders
ANALYZE: Separation of concerns (src/, lib/, utils/, components/, services/)
ANALYZE: Monorepo patterns (packages/, apps/, libs/)
ANALYZE: Config-driven patterns (config/, .env*, settings/)

STORE: architecture = {
  pattern: "<monolith|monorepo|microservices|library>",
  top_level_dirs: [],
  separation_of_concerns: "<good|moderate|poor>",
  config_driven: <boolean>
}
```

---

## Step 10: Compile Inventory

```json
{
  "subject": "{subject_name}",
  "type": "codebase",
  "generatedAt": "<ISO-8601>",
  "source": "{source}",
  "method": "local-filesystem-scan",
  "languages": ["typescript", "python"],
  "frameworks": ["react", "next.js"],
  "package_manager": "npm",
  "file_counts": {
    "total_files": 1234,
    "total_dirs": 89,
    "ts": 450,
    "js": 120,
    "py": 0,
    "md": 67,
    "yaml": 23,
    "json": 45
  },
  "loc": {
    "code": 45000,
    "docs": 8000,
    "total": 53000
  },
  "agents": [],
  "workflows": [],
  "tasks": [],
  "testing": {},
  "documentation": {},
  "automation": {},
  "architecture": {},
  "dependencies": {
    "production": [],
    "development": []
  }
}
```

---

## Step 11: Write Outputs

```
ACTION: Write("{output_dir}/inventory-{subject_name}.json", JSON.stringify(inventory, null, 2))
ACTION: Write("{output_dir}/inventory-{subject_name}.md", markdown_summary)
```

The markdown summary should include:
- Subject identification
- Key metrics table (files, LOC, languages)
- Architecture overview
- Testing & automation status
- Notable patterns

---

## Outputs

| File | Location | Format |
|------|----------|--------|
| Subject inventory | `{output_dir}/inventory-{subject_name}.json` | JSON |
| Subject summary | `{output_dir}/inventory-{subject_name}.md` | MD |

## Veto Conditions

1. **No source available** — No URL or path provided → HALT
2. **Clone fails** — git clone returns error → HALT
3. **Empty repository** — Zero files found after clone → HALT
4. **No read access** — Cannot read files in subject_root → HALT

## Verification

- [ ] JSON inventory file is valid (parseable)
- [ ] File counts match real filesystem (spot-check 2 extensions)
- [ ] Languages correctly detected
- [ ] All sections populated (no empty objects without reason)
- [ ] LOC count is reasonable (not zero for non-empty repo)
- [ ] Source path correctly recorded
