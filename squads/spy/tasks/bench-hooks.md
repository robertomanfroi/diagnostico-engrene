# Task: Hook/Lifecycle System Deep Comparison (Autonomous)

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
id: bench-hooks
name: "Hook System Deep Comparison"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "15-20min"
description: "Deep comparison of hook/lifecycle/event systems between AIOX and competitor"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Many AI frameworks implement hook or lifecycle systems (pre/post execution events,
user prompt hooks, tool call interceptors, etc.). This task produces a deep comparison
when a competitor has a hook system worth analyzing.

## When to Execute

- Competitor has hooks, lifecycle events, or plugin system
- Triggered by `*bench-hooks {competitor}`
- Also triggered automatically during `*bench` if hooks detected in competitor scan

## Reference

See `docs/bench/pai/pai-hooks-system-analise-profunda.md` for output format.

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
  HALT: "Cannot analyze hooks without local clone."

All subsequent steps use Glob/Read/Grep on competitor_root.
NEVER use WebFetch for competitor structural data.
NEVER estimate. NEVER invent file contents or paths.
```

---

## Step 1: Detect Competitor Hook System

```
ACTION: Grep("../bench/{competitor}/", "hook|Hook|lifecycle|Lifecycle|event|Event|middleware", type="ts,js,md,yaml")
STORE: hook_files[]

IF hook_files.length == 0:
  REPORT: "Competitor does not have a detectable hook/lifecycle system"
  HALT

ACTION: For each hook_file, Read and categorize:
  - Hook definitions (what events exist)
  - Hook implementations (what they do)
  - Hook registration (how to add custom hooks)
  - Hook execution order (priority/sequence)
```

---

## Step 2: Map Competitor Hook Taxonomy

Build complete hook catalog:

```markdown
| Hook Name | Trigger Point | Purpose | Async? | Blocking? |
|-----------|--------------|---------|--------|-----------|
| {name} | {when it fires} | {what it does} | {yes/no} | {yes/no} |
```

Categories:
- **Session hooks:** start, end, resume
- **Prompt hooks:** pre-submit, post-submit, sentiment
- **Tool hooks:** pre-call, post-call, error
- **Agent hooks:** activation, deactivation, handoff
- **Quality hooks:** pre-commit, post-review, rating
- **Learning hooks:** feedback capture, pattern storage

---

## Step 3: Map AIOX Hook Equivalent

```
ACTION: Grep(".aiox-core/", "hook|lifecycle|event|trigger|pre-|post-")
ACTION: Grep(".claude/", "hook|PreToolUse|PostToolUse|UserPromptSubmit")
NOTE: AIOX hooks are scanned locally. Competitor hooks from ../bench/{competitor}/
ACTION: Read(".claude/settings.json") → check hooks configuration

STORE: aiox_hooks[]
```

Map:
```markdown
| Competitor Hook | AIOX Equivalent | Status | Gap |
|----------------|----------------|--------|-----|
| {comp_hook} | {aiox_equiv or "none"} | Forte/Parcial/Sem equiv | {what's missing} |
```

---

## Step 4: Analyze Hook Implementation Depth

For each competitor hook category, analyze:

```markdown
## {Category}: {Hook Name}

### Implementacao no {Competitor}

**Codigo de referencia:** `{file_path}`

```typescript
{key implementation code, max 30 lines}
```

**Comportamento:**
- Trigger: {when}
- Input: {what data it receives}
- Output: {what it produces}
- Side effects: {storage, notifications, etc}

### Estado no AIOX

**Equivalente:** {description or "nenhum"}
**Gap:** {what AIOX lacks}
**Valor de implementar:** {why it matters}
**Complexidade:** {Baixa/Media/Alta}

### Recomendacao

{Absorb / Skip / Adapt}
- {justification}
```

---

## Step 5: Build Degradation Matrix

If competitor hooks provide capability that AIOX achieves differently:

```markdown
## Matriz de Degradacao

| Capability | Com Hooks ({Competitor}) | Sem Hooks (AIOX) | Impacto |
|-----------|------------------------|-------------------|---------|
| {capability} | {how competitor does it} | {how AIOX handles it} | {Alto/Medio/Baixo} |
```

---

## Step 6: Write Output

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-hooks-system-analise-profunda.md`

Structure:
1. Visao geral (hook count, categories)
2. Taxonomia completa do competidor
3. Mapeamento AIOX equivalente
4. Deep dive por categoria
5. Matriz de degradacao
6. Recomendacoes de absorcao
7. Impacto no roadmap

---

## Outputs

| File | Format |
|------|--------|
| `{competitor}-hooks-system-analise-profunda.md` | MD |

## Verification

- [ ] All competitor hooks identified and cataloged
- [ ] AIOX equivalent checked for each
- [ ] Code references are real (not invented)
- [ ] Degradation matrix covers key capabilities
- [ ] Recommendations are actionable
