> **DEPRECATED:** This task is superseded by `bench-matrix.md` (universal comparison matrix). For codebase comparisons, use `bench-codebase-recon.md` + `bench-matrix.md`. The "quick" profile in `bench-comparison-pipeline.yaml` replaces this task's functionality.

# Task: Quick Framework Comparison (Autonomous)

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
id: bench-quick-compare
name: "Quick Framework Comparison"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "8-12min"
description: "Autonomous structural comparison of agents and workflows between AIOX and a competitor"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Rapid competitive comparison producing 3 core artifacts.
Uses real file scanning for AIOX and best-available source for competitor.

## Inputs

```yaml
inputs:
  competitor_name: { type: string, required: true }
  source_type: { type: enum, values: [repo_local, repo_github] }
  source_path: { type: string, required: true, description: "Local path or GitHub URL (will be cloned)" }
```

## CRITICAL: Local Clone Rule

**Every benchmark MUST work from a locally cloned repository.**

```
IF source_type = repo_github AND local clone does not exist:
  ACTION: Bash("git clone {source_path} .bench-repos/{competitor_name}")
  STORE: local_path = .bench-repos/{competitor_name}

IF source_type = repo_local:
  ACTION: Bash("ls {source_path}")  # verify exists
  STORE: local_path = source_path

All subsequent steps use Glob/Read on local_path. NEVER use WebFetch for competitor data.
NEVER estimate counts. Count real files.
```

---

## Step 1: Load AIOX Baseline

IF `docs/bench/appendix-aiox-agent-command-inventory.json` exists AND is less than 7 days old:
```
ACTION: Read("docs/bench/appendix-aiox-agent-command-inventory.json")
STORE: aiox_agents[]
```

ELSE:
```
ACTION: Execute task bench-inventory.md
THEN: Read generated inventory
```

Similarly for workflows:
```
ACTION: Read("docs/bench/appendix-aiox-workflow-sequence-inventory.json")
STORE: aiox_workflows[]
```

---

## Step 2: Scan Competitor Structure

### If source_type = repo_local

```
ACTION: Glob("{source_path}/**/agents/*.md") OR Glob("{source_path}/**/personas/*.md")
STORE: comp_agent_files[]

ACTION: Glob("{source_path}/**/workflows/*.yaml") OR Glob("{source_path}/**/workflows/*.md")
STORE: comp_workflow_files[]

ACTION: Glob("{source_path}/**/tasks/*.md") OR Glob("{source_path}/**/skills/*/SKILL.md")
STORE: comp_task_files[]
```

For EACH comp_agent_file:
```
ACTION: Read(file_path, limit=80)
EXTRACT: agent name/id, role, commands list, tier/type
STORE: comp_agents[]
```

For EACH comp_workflow_file:
```
ACTION: Read(file_path, limit=100)
EXTRACT: workflow name, phases/steps, agents involved
STORE: comp_workflows[]
```

### If source_type = repo_github

```
ACTION: Bash("gh api repos/{owner}/{repo}/git/trees/main?recursive=1 | head -500")
EXTRACT: File tree structure
IDENTIFY: agent files, workflow files, task files by path pattern

ACTION: For key agent files, use WebFetch to read raw content:
  WebFetch("https://raw.githubusercontent.com/{owner}/{repo}/main/{agent_path}", "Extract agent name, role, and list of commands")
```

### If source_type = docs_url

```
ACTION: WebFetch("{source_path}", "Extract complete list of agents, their roles, commands, and workflows")
STORE: parsed_data

IF llms-full.txt available:
  ACTION: WebFetch("{base_url}/llms-full.txt", "Extract all agent definitions, workflow names, and command lists")
```

### If source_type = npm_package

```
ACTION: Bash("npm view {package_name} dist.tarball")
ACTION: Bash("npm pack {package_name} --pack-destination /tmp/bench-{competitor}")
ACTION: Bash("tar -xzf /tmp/bench-{competitor}/*.tgz -C /tmp/bench-{competitor}/")
THEN: Proceed as repo_local with extracted path
```

---

## Step 3: Build Agent Matrix

For each competitor agent, find AIOX equivalent:

```
ALGORITHM:
1. Exact name match (analyst→analyst) = Forte candidate
2. Role similarity match (ux-expert→ux-design-expert) = Forte candidate
3. Command overlap > 60% = Parcial candidate
4. No match found = Sem equivalente

SCORING (Paridade 1-5):
  5/5: Same name + same role + command overlap > 80%
  4/5: Same role + command overlap > 60%
  3/5: Similar role + command overlap > 40%
  2/5: Weak similarity, different scope
  1/5: No meaningful equivalent
```

Build matrix table:

```markdown
| {Competitor} agent | AIOX equivalente | Paridade | Delta objetivo |
| --- | --- | --- | --- |
| `{comp_agent}` | `{aiox_agent}` | {score}/5 | {specific differences} |
```

ALSO identify:
- AIOX agents WITHOUT competitor equivalent (AIOX differentials)
- Competitor agents WITHOUT AIOX equivalent (gaps)

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-vs-aiox-agents-command-matrix.md`

Format: Follow exact structure from `docs/bench/bmad/bmad-vs-aiox-agents-command-matrix.md`

---

## Step 4: Build Workflow Matrix

For each competitor workflow, find AIOX equivalent:

```
ALGORITHM:
1. Name match (greenfield-fullstack→greenfield-fullstack)
2. Type match (greenfield→greenfield variants)
3. Purpose match by step analysis

SCORING: Same 1-5 scale as agents
```

Build matrix:

```markdown
| {Competitor} workflow | AIOX workflow | Paridade | Leitura objetiva |
| --- | --- | --- | --- |
```

List AIOX-only workflows (differentials)

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-vs-aiox-workflow-step-matrix.md`

Format: Follow exact structure from `docs/bench/bmad/bmad-vs-aiox-workflow-step-matrix.md`

---

## Step 5: Compile Comparativo Completo

Combine Steps 3 and 4 into unified document:

```markdown
# {Competitor} vs AIOX {version} - Comparativo Profundo

Data: {today}
Escopo: comparacao tecnica profunda de agentes, workflows e capacidades operacionais

## Fontes (oficiais)
- {competitor source citations}
- AIOX local: .aiox-core/development/

## Metodo de comparacao
1. {how competitor was scanned}
2. AIOX: filesystem scan direto
3. Mapeamento em 3 niveis: Forte / Parcial / Sem equivalente

## Inventario real atual

### {Competitor}
| Componente | Quantidade |
|------------|------------|
| Agents | {count} |
| Workflows | {count} |
| Tasks/Commands | {count} |

### AIOX
| Componente | Quantidade |
|------------|------------|
| Agents | {count} |
| Workflows | {count} |
| Tasks | {count} |
| Commands | {count} |

## Matriz 1:1 - Agentes
{from Step 3}

## Matriz 1:1 - Workflows
{from Step 4}

## Gaps AIOX (diferenciais exclusivos)
{AIOX features not in competitor}

## Gaps {Competitor} (sem equivalente AIOX)
{Competitor features not in AIOX}

## Leitura objetiva
{3-5 bullet points, brutally honest}
```

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-vs-aiox-comparativo-completo.md`

---

## Outputs

| # | File | Format |
|---|------|--------|
| 1 | `{competitor}-vs-aiox-agents-command-matrix.md` | MD |
| 2 | `{competitor}-vs-aiox-workflow-step-matrix.md` | MD |
| 3 | `{competitor}-vs-aiox-comparativo-completo.md` | MD |

## Verification

- [ ] Agent matrix covers ALL competitor agents
- [ ] Agent matrix covers ALL AIOX agents
- [ ] Workflow matrix covers ALL competitor workflows
- [ ] Paridade scores justified with specific delta
- [ ] Sources cited for every competitor data point
- [ ] AIOX data matches actual filesystem
