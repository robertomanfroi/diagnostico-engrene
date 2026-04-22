# Pipeline Runner Checklist — Post-Mortem Domain Decoder

Checklist obrigatório para validar pipelines gerados por `*create-pipeline`.
Baseado em 14 bugs encontrados no domain-decoder pipeline (2026-03-31).

**Cada item tem um BUG-REF** apontando para o bug que motivou a regra.
Referência completa: `docs/research/2026-03-31-decoder-pipeline-lessons-learned/01-bug-catalog.md`

---

## SEÇÃO 1: Deliverables Obrigatórios (VETO se ausente)

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 1.1 | `scripts/{squad}.sh` existe e é executável (`chmod +x`) | B01 | |
| 1.2 | `templates/pipeline/prompt.md` existe com placeholders `{SYSTEM_DIR}`, `{SOURCE_PATH}`, `{FORCE_PHASE}` | B01 | |
| 1.3 | `.sh` aceita `--source <path>` | B03 | |
| 1.4 | `.sh` aceita `--model <name>` | B01 | |
| 1.5 | `.sh` aceita `--phase <num>` | B01 | |
| 1.6 | `.sh --help` parseia sem erro | B01 | |
| 1.7 | Agent summaries existem em `agents/summaries/*.md` (~2K chars cada) | Gap5 | |

---

## SEÇÃO 2: Comportamento do Runner (.sh)

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 2.1 | Modo default = `auto` (detecta greenfield/brownfield via state file) | B02 | |
| 2.2 | Slug auto-derivado do `--source` (não é argumento posicional obrigatório) | B03 | |
| 2.3 | Versão auto-detectada do source (package.json → config.yaml → fallback) | B04 | |
| 2.4 | Gate validation roda ANTES de marcar fase como "complete" | B05 | |
| 2.5 | Se gate falha, status reverte para "in_progress" (não fica "complete") | B05 | |

---

## SEÇÃO 3: Stdout e Output Handling

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 3.1 | JSON metadata de `claude -p` é filtrado (`grep -v '^{"type":"result"'`) | B10 | |
| 3.2 | Script salva TODO output >200 chars automaticamente (não depende do LLM usar Write) | B11 | |
| 3.3 | `<promise>PHASE_COMPLETE</promise>` é buscado apenas nas últimas 30 linhas | B07 | |
| 3.4 | Completion threshold é por fase (3000-4000 chars), não fixo em 500 | B10, B11 | |

---

## SEÇÃO 4: Context e Turns

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 4.1 | `--max-turns` escalado por modelo: haiku≥12, sonnet≥10, opus≥15 | B12 | |
| 4.2 | `--allowedTools` restrito (Read, Write, Glob, Grep, Bash limitado) | B12 | |
| 4.3 | Prior phase outputs injetados INLINE no prompt (não como paths para o LLM ler) | B13 | |
| 4.4 | Prior outputs truncados (~3KB por arquivo) para controle de context | B12 | |
| 4.5 | Task content injetado inline via `build_task_content()` (LLM não gasta turn lendo) | Gap3 | |
| 4.6 | Agent summary injetado inline via `build_agent_summary()` | Gap5 | |
| 4.7 | Checklists injetados inline para fase de validação | Gap3 | |

---

## SEÇÃO 5: Gates e Markers

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 5.1 | VETO/BLOCKED/FAILED regex usa contexto (`^VETO` ou `status:\s*VETO`), não substring | B06 | |
| 5.2 | `find -exec grep` em vez de glob `*.md` para dirs potencialmente vazios | B08 | |
| 5.3 | `jq` usa `--arg` para todas variáveis (nunca interpola shell vars direto) | B09 | |
| 5.4 | E7-style gates (arquivo separado opcional) são WARNING, não BLOCKING | B14 | |
| 5.5 | Gates que exigem arquivo separado documentam fallback (pode estar inline no output) | B14 | |

---

## SEÇÃO 6: Retry e Resiliência

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 6.1 | Retry boost na iter 2+: prompt informa o que faltou (chars, files, artifacts) | B10, B14 | |
| 6.2 | Retry boost informa quantos arquivos já foram criados | B14 | |
| 6.3 | Max iterations configurável (default 10) | — | |
| 6.4 | Circuit breaker: abort após N falhas consecutivas | — | |

---

## SEÇÃO 7: Prompt Template (prompt.md)

| # | Check | BUG-REF | PASS/FAIL |
|---|-------|---------|-----------|
| 7.1 | Template NÃO pede para o LLM ler task files (conteúdo é injetado) | Gap3 | |
| 7.2 | Template NÃO pede para o LLM ler agent files (summary é injetado) | Gap5 | |
| 7.3 | Template lista artifacts OBRIGATÓRIOS por fase com paths exatos | B01, B14 | |
| 7.4 | Template declara "under 3000 chars is incomplete" | B10, B11 | |
| 7.5 | Template inclui budget de turns visível ao LLM | B12 | |
| 7.6 | Template tem placeholders: `{AGENT_SUMMARY}`, `{TASK_CONTENT}`, `{CHECKLIST_CONTENT}` | Gap3, Gap5 | |
| 7.7 | Template diz "Do NOT re-read prior outputs — they are already in your context" | B13 | |

---

## SEÇÃO 8: Claude Code Runtime Constraints

Regras extraídas do source code do Claude Code CLI (212 rules, 89.8% SBVR compliant).
Referência completa: `.claude/rules/headless-pipeline.md`

| # | Check | RULE-REF | PASS/FAIL |
|---|-------|----------|-----------|
| 8.1 | `--dangerously-skip-permissions` usado em toda chamada `claude -p` | R1 (BR-PERM-065) | |
| 8.2 | Runner NÃO instrui LLM a escrever em paths protegidos (`.git/`, `.claude/`, `.vscode/`, shell configs) | R2 (BR-PERM-053) | |
| 8.3 | `--allowedTools` declarado explicitamente (não usa default) | R4 (BR-TOOL-001) | |
| 8.4 | Prior context truncado a ~3KB/arquivo (evitar truncamento do tool result 50K limit) | R5 (BR-CONST-001) | |
| 8.5 | JSON metadata filtrado do stdout (`grep -v '^{"type":"result"'`) | R8 | |
| 8.6 | Prompt instrui "Read source files FIRST, then write artifacts" | R9 (BR-PROMPT-006) | |
| 8.7 | Compound commands <50 subcommands | R7 (BR-BASH-PERM-LIMIT) | |

---

## Scoring

| Score | Veredicto |
|-------|-----------|
| 37/37 | PASS — Pipeline runner production-ready |
| 31-36 | PASS WITH WARNINGS — Issues menores documentados |
| 25-30 | CONDITIONAL — Fixes obrigatórios antes de uso em produção |
| <25 | FAIL — Requer redesign |

---

## Uso

Este checklist deve ser executado por `create-pipeline-validate` como último step.
Se o score < 25, o validate deve retornar FAIL com a lista de items faltantes.

---

*Checklist v1.0 — Baseado no post-mortem de 14 bugs (2026-03-31)*
*Fonte: docs/research/2026-03-31-decoder-pipeline-lessons-learned/*
