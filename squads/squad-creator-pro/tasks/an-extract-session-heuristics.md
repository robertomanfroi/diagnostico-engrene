---
task-id: an-extract-session-heuristics
name: "Extrair Heurísticas de Sessão de Trabalho"
version: 3.1.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Requer síntese de padrões implícitos em execução real — Opus para profundidade"
estimated-time: 15 min
complexity: medium
agent: "@oalanicolas"
process_id: "SP-EXTRACT-SESSION-HEURISTICS"
mode: VALIDAR
parent_task: an-extract-heuristics
parent_relationship: "specialization — herda Pareto ao Cubo, SE/ENTÃO format, 3-Layer, Quality Check; adiciona session eligibility, git worker, cross-session triangulation, hook integration"

inputs:
  required:
    - session_context: "Auto-gerado pelo Worker de contexto OU fornecido manualmente"
  optional:
    - epic_id: "Epic ID se houver (ex: Epic 71)"
    - handoff_file: "Path para handoff da sessão (se existir)"
    - existing_heuristics: "Path para heurísticas existentes (default: minds/oalanicolas/heuristics/)"

outputs:
  primary:
    - heuristics_files: "Arquivos AN_KE_NNN.md no formato padrão"
    - decision_cards: "Entries em decision-cards.yaml (L2)"
    - extraction_report: "Resumo: N candidatas → N formalizadas, classificação Pareto"
  secondary:
    - memory_update: "Atualização do MEMORY.md do projeto com referência"
    - token_updates: "Novos tokens se thresholds/comportamentos emergirem"

hook_integration:
  trigger: "manual (human invokes after session)"
  location: ".claude/hooks/post-session-heuristics.sh"
  auto_extract: false  # NEVER auto-extract. Human gate is non-negotiable.
  behavior: |
    1. Hook checks eligibility (deterministic, $0, <1s):
       - Filters out runner/mechanical commits (sinkra-map, outputs, score_cards)
       - Counts only HUMAN decision commits (feat/refactor/fix non-mechanical)
       - Checks duration ≥30min, human decisions ≥2, code files ≥5
       - If runner_ratio >70% → skip (runner session)
    2. If eligible: SUGGESTS to human, shows what was found
    3. Human decides: /extract-session-heuristics OR skip
    4. NEVER extracts without explicit human approval
  rationale: |
    90% das sessões são runners autônomos (sinkra-map, mmos, copy) que geram
    50+ commits mecânicos. Auto-extract iria gerar heurísticas de lixo.
    AN_KE_002: "Se entrar cocô, sai cocô."

memory_routing:
  heuristic_file: "squads/squad-creator-pro/minds/oalanicolas/heuristics/AN_KE_NNN.md"
  decision_cards: "squads/squad-creator-pro/minds/oalanicolas/heuristics/decision-cards.yaml"
  project_memory: "~/.claude/projects/{project}/memory/MEMORY.md"
  memory_entry_format: "- [Heuristics AN_KE_NNN-NNN](file.md) — one-line hook"

checklist: "checklists/session-heuristics-extraction.md"
template: "templates/session-heuristic-tmpl.md"
elicit: false
---

# SP-EXTRACT-SESSION-HEURISTICS — Processo de Extração de Heurísticas de Sessão

> **Processo SINKRA mapeado.** Não é uma task solta — é um pipeline de 5 fases
> com tokens, checkpoints e composição formal.
>
> **Parent task:** `an-extract-heuristics` (SP-EXTRACT-HEURISTICS) — framework base para extração de experts.
> Esta é uma **especialização** que extrai de sessões de execução (o que aprendemos fazendo).
> Herda: Pareto ao Cubo, SE/ENTÃO/NUNCA format, 3-Layer (L1/L2/L3), Quality Check pattern.
> Adiciona: Session Eligibility, git worker, cross-session triangulation, hook integration.
>
> **Princípio:** "Curadoria > Volume. Se entrar cocô, sai cocô."

---

## Process Tokens

```yaml
tokens:
  - token_id: "TKN-ESH-THR-001"
    family: Threshold
    name: min_source_traceability
    value: 100
    unit: "%"
    description: "Todas as heurísticas DEVEM ter [SOURCE:]. Zero tolerância."
    consumed_by: ["phase_4_formalize", "quality_check"]

  - token_id: "TKN-ESH-THR-002"
    family: Threshold
    name: min_candidatas_brutas
    value: 5
    description: "Mínimo de candidatas brutas antes de filtrar. Se < 5, sessão não teve profundidade suficiente."
    consumed_by: ["phase_1_identify"]

  - token_id: "TKN-ESH-THR-003"
    family: Threshold
    name: max_generico_ratio
    value: 30
    unit: "%"
    description: "Se > 30% das candidatas são genéricas (💩), a varredura está rasa. Aprofundar."
    consumed_by: ["phase_2_filter"]

  - token_id: "TKN-ESH-THR-004"
    family: Threshold
    name: min_quality_check_score
    value: 5
    unit: "de 6"
    description: "Score mínimo no quality check para aprovar extração."
    consumed_by: ["quality_check"]

  - token_id: "TKN-ESH-BEH-001"
    family: Behavior
    name: overlap_action
    value: "update_existing"
    description: "SE heurística duplica existente COM nova evidência → ATUALIZAR, não criar nova."
    consumed_by: ["phase_3_overlap"]

  - token_id: "TKN-ESH-BEH-002"
    family: Behavior
    name: triangulation_promotion
    value: "3_sessions_promote"
    description: "SE 3+ sessões confirmam mesma heurística → ELEVAR zona (20% → 4%, 4% → 0,8%)."
    consumed_by: ["phase_3_overlap"]

  - token_id: "TKN-ESH-TAX-001"
    family: Taxonomy
    name: heuristic_types
    value: ["Decision Heuristic", "Veto Heuristic", "Architecture Heuristic", "Observability Heuristic", "State Management Heuristic"]
    description: "Tipos válidos de heurística. Toda nova deve encaixar em um desses."
    consumed_by: ["phase_4_formalize"]

  - token_id: "TKN-ESH-TAX-002"
    family: Taxonomy
    name: pareto_zones
    value:
      genialidade: "0.8% — muda paradigma"
      excelencia: "4% — guardrail que previne retrabalho"
      impacto: "20% — boa prática que acelera"
      merda: "80% — genérico, sem evidência, descartar"
    description: "Classificação obrigatória via Pareto ao Cubo."
    consumed_by: ["phase_2_filter"]

  - token_id: "TKN-ESH-ACC-001"
    family: Accountability
    name: extractor
    value: "@oalanicolas"
    description: "Knowledge Architect é accountable pela qualidade da extração."
    consumed_by: ["all_phases"]

  # ── Gap #3: Session Eligibility ──
  - token_id: "TKN-ESH-THR-005"
    family: Threshold
    name: session_min_duration_minutes
    value: 30
    description: "Sessão < 30min não merece extração. Typo fixes não geram heurísticas."
    consumed_by: ["hook_integration", "phase_0_eligibility"]

  - token_id: "TKN-ESH-THR-006"
    family: Threshold
    name: session_min_decisions
    value: 2
    description: "Sessão precisa de ≥2 decisões de arquitetura/pivot pra justificar extração."
    consumed_by: ["hook_integration", "phase_0_eligibility"]

  - token_id: "TKN-ESH-THR-007"
    family: Threshold
    name: session_min_files_changed
    value: 5
    description: "Sessão com <5 arquivos modificados provavelmente não tem profundidade."
    consumed_by: ["hook_integration"]

  # ── Gap #6: Evidence Append ──
  - token_id: "TKN-ESH-BEH-003"
    family: Behavior
    name: evidence_append_format
    value: "\"[SOURCE: sessão {id}, {project}] '{evidência concreta verbal}'\""
    description: "Formato padronizado para append de evidence em heurísticas existentes."
    consumed_by: ["phase_3_overlap"]

  - token_id: "TKN-ESH-THR-008"
    family: Threshold
    name: max_evidence_entries
    value: 10
    description: "Máximo de evidence entries por heurística. Acima disso, consolidar."
    consumed_by: ["phase_3_overlap"]
```

---

## Session Eligibility (Phase 0 — Gate)

Antes de iniciar a extração, verificar se a sessão merece:

```yaml
session_eligibility:
  min_duration: 30  # TKN-ESH-THR-005
  min_decisions: 2   # TKN-ESH-THR-006
  min_files_changed: 5  # TKN-ESH-THR-007
  skip_if:
    - "only docs/ changes (no code)"
    - "only outputs/ changes (artifacts, not decisions)"
    - "only typo/formatting fixes"
    - "session < 30 minutes"
```

**Worker de contexto automático (Gap #3):**

```bash
# Gerar contexto da sessão automaticamente ($0, <2s)
SESSION_COMMITS=$(git log --since="3 hours ago" --oneline 2>/dev/null | head -20)
SESSION_FILES=$(git diff --stat HEAD~10 2>/dev/null | tail -5)
SESSION_DURATION_ESTIMATE=$(git log --since="3 hours ago" --format="%ar" 2>/dev/null | tail -1)
FILES_CHANGED=$(git diff --stat HEAD~10 2>/dev/null | tail -1 | grep -oE '[0-9]+ file' | grep -oE '[0-9]+')

# Eligibility check
if [[ "${FILES_CHANGED:-0}" -lt 5 ]]; then
  echo "SKIP: <5 files changed"
  exit 0
fi

# Gerar contexto compacto
cat <<EOF
Session Context (auto-generated):
- Commits: $(echo "$SESSION_COMMITS" | wc -l | tr -d ' ')
- Files changed: ${FILES_CHANGED:-0}
- Duration estimate: ${SESSION_DURATION_ESTIMATE:-unknown}
- Recent commits:
$SESSION_COMMITS
- Files summary:
$SESSION_FILES
EOF
```

---

## Veto Conditions

| ID | Condition | Token | Action |
|----|-----------|-------|--------|
| VETO-ESH-001 | Heurística sem [SOURCE:] | TKN-ESH-THR-001 | BLOCK — adicionar evidência ou descartar |
| VETO-ESH-002 | Heurística inferida sem evidência empírica | TKN-ESH-THR-001 | BLOCK — precisa de caso real, não teoria |
| VETO-ESH-003 | Heurística duplica existente sem nova evidência | TKN-ESH-BEH-001 | BLOCK — atualizar existente em vez de criar nova |
| VETO-ESH-004 | < 5 candidatas brutas (sessão rasa) | TKN-ESH-THR-002 | BLOCK — aprofundar varredura antes de filtrar |
| VETO-ESH-005 | > 30% candidatas genéricas | TKN-ESH-THR-003 | WARN — varredura rasa, re-analisar com perguntas-guia |

---

## Phase 1: IDENTIFY — Varredura de Candidatas (5 min)

**Executor:** @oalanicolas
**Input:** session_context (conversa, handoff, commits, bugs)
**Output:** Lista de 5-15 candidatas brutas

### Fontes de Heurísticas (5 categorias)

| Categoria | O que procurar | Exemplo |
|-----------|---------------|---------|
| **Decisões pivot** | Momentos que mudaram o rumo | "Comparamos validate-skill vs validate-squad → gap analysis gerou roadmap" |
| **Bugs/Incidentes** | Erros que revelaram regras | "Bug ${} quoting → 'testar módulo isolado, não pipeline'" |
| **Anti-patterns evitados** | O que quase deu errado | "Quase removemos post-process.sh → 'audit gate antes de cleanup'" |
| **Patterns validados** | O que funcionou e por quê | "Batch fix mecânico 19% → 94% → 'mecânico primeiro, hardening depois'" |
| **Research insights** | Confirmação/refutação externa | "Anthropic paper confirma composable > frameworks" |

### Perguntas-guia (Critical Decision Method)

```
1. "O que deu certo que NÃO ERA ÓBVIO antes desta sessão?"
2. "O que quase deu errado? Em que PONTO EXATO evitamos?"
3. "O que faríamos DIFERENTE na próxima vez?"
4. "Que regra SE/ENTÃO emergiu que não tínhamos antes?"
5. "Que suposição foi INVALIDADA por dados empíricos?"
6. "Que padrão se REPETIU 2+ vezes durante a sessão?"
```

### Checkpoint Phase 1

```yaml
gate: "candidatas >= TKN-ESH-THR-002 (5)"
pass: "Prosseguir para Phase 2"
fail: "VETO-ESH-004 — sessão insuficiente, precisa de mais contexto"
```

---

## Phase 2: FILTER — Pareto ao Cubo (3 min)

**Executor:** @oalanicolas
**Input:** Lista de candidatas brutas
**Output:** Lista filtrada com classificação por zona

### Classificação

| Zona | Critério | Ação | Emoji |
|------|----------|------|-------|
| **0,8% Genialidade** | Muda paradigma. Sem isso, o trabalho seria fundamentalmente diferente. | FORMALIZAR primeiro | 🧠 |
| **4% Excelência** | Guardrail que previne retrabalho significativo | FORMALIZAR | 💎 |
| **20% Impacto** | Boa prática que acelera | FORMALIZAR se tiver [SOURCE:] forte | 🔥 |
| **80% Merda** | Óbvio, genérico, sem evidência específica | DESCARTAR | 💩 |

### Teste de Genericidade (anti-💩)

```
SE a heurística funciona pra QUALQUER projeto sem contexto específico
→ Provavelmente genérica demais (💩)

SE a heurística só faz sentido DENTRO DO CONTEXTO desta sessão
→ Provavelmente valiosa (🔥💎🚀)

Boas heurísticas = contexto específico + evidência empírica + dados
```

### Checkpoint Phase 2

```yaml
gate: "generico_ratio <= TKN-ESH-THR-003 (30%)"
pass: "Prosseguir para Phase 3"
warn: "VETO-ESH-005 — re-analisar candidatas com perguntas-guia mais profundas"
```

---

## Phase 3: OVERLAP — Dedup + Triangulação (3 min)

**Executor:** @oalanicolas
**Input:** Lista filtrada
**Output:** Lista deduplicada (novas vs updates)

### Procedimento

```bash
# 1. Listar existentes
ls squads/squad-creator-pro/minds/oalanicolas/heuristics/ | sort

# 2. Para cada candidata:
#    a. Grep pela regra SE/ENTÃO nas existentes
#    b. Se match → verificar se sessão traz NOVA evidência
#    c. Se nova evidência → ATUALIZAR existente (adicionar evidence block)
#    d. Se sem match → CRIAR nova
```

### Triangulação (TKN-ESH-BEH-002)

```
SE 3+ sessões diferentes confirmam a mesma heurística
→ ELEVAR zona: 20% Impacto → 4% Excelência (ou 4% → 0,8%)
→ Adicionar nota: "Confirmada por N sessões independentes"
```

### Evidence Append Format (Gap #6 — TKN-ESH-BEH-003)

Quando atualizando heurística existente com nova evidência:

```markdown
## Evidence

    - "[SOURCE: sessão 8b1f20d, mmos] 'Batch fix 29 frontmatters: 19% → 94% PASS em 5min'"
    - "[SOURCE: sessão 9c3ca5e, mmos] 'yaml-repair.py desbloqueou Opus (0% → 67%)'"
```

**Regras:**
- Adicionar no final do bloco `evidence` do YAML na seção `## Configuration`
- Formato: `- "[SOURCE: sessão {id}, {projeto}] '{citação ou fato verbatim}'"`
- Máximo TKN-ESH-THR-008 (10) entries. Acima disso, consolidar as mais antigas.
- Se evidence contradiz a heurística → REAVALIAR a regra, não apenas appendar.

### Output

```yaml
dedup_result:
  new_heuristics: N      # criar AN_KE_NNN.md
  updated_existing: N    # adicionar evidence a AN_KE existente
  promoted: N            # zona elevada por triangulação
  discarded: N           # duplicata sem nova evidência
```

---

## Phase 4: FORMALIZE — 3 Camadas (4 min)

**Executor:** @oalanicolas
**Input:** Lista deduplicada
**Output:** L2 decision card (YAML) + L3 arquivo .md

### 3-Layer Format

| Camada | Formato | Propósito | Quando consultar |
|--------|---------|-----------|-----------------|
| **L1** | 3 campos inline no agente | Decisão rápida em runtime | Sempre — carregado com o agente |
| **L2** | ~8 campos em `decision-cards.yaml` | Decisão informada com evidence | Quando L1 não basta |
| **L3** | 40-80 linhas em AN_KE_NNN.md | Documentação completa, onboarding | Nunca em runtime — só referência |

**OBRIGATÓRIO:** Criar L2 (decision card) E L3 (.md). L1 é atualizado quando o agente é re-synced.

### Step 4a: Adicionar Decision Card (L2)

Em `minds/oalanicolas/heuristics/decision-cards.yaml`, adicionar:

```yaml
- id: AN_KE_NNN
  name: "Nome"
  rule: "SE {condição} → ENTÃO {ação}"
  zone: "{genialidade|excelencia|impacto}"
  trigger: "{quando se aplica}"
  anti_pattern: "{o que acontece quando ignora}"
  evidence: "{dado empírico com números [SOURCE:]}"
```

### Step 4b: Criar Arquivo .md (L3)

### Template

```markdown
# AN_KE_NNN - Nome da Heurística

**Type:** {TKN-ESH-TAX-001 — um dos tipos válidos}
**Zone:** {TKN-ESH-TAX-002 — 🧠|💎|🔥}
**Agent:** @oalanicolas
**Source:** [SOURCE: sessão {id}, {project} — descrição/contexto da sessão]

## Purpose

{Parágrafo substancial explicando o PROBLEMA que resolve, QUANDO se aplica, e POR QUE é específico (não genérico). Incluir exemplos contextuais da sessão onde ocorreu.}

## Configuration

\```yaml
AN_KE_NNN:
  name: "Nome da Heurística"
  zone: "{genialidade|excelencia|impacto}"
  trigger: "Quando esta heurística se aplica (condições exatas)"

  rule: |
    SE {condição observável no trabalho/código/planning}
    ENTÃO {ação específica de mitigação/decisão}
    NUNCA {anti-pattern ou abordagem ingênua correspondente}

  veto_condition:
    trigger: "O que caracteriza a quebra flagrante da regra"
    action: "VETO — Pesar: {Ação de emergência para bloquear e corrigir}"

  evidence:
    - "[SOURCE: sessão {id}, {project}] '{citação verbatim 1}'"
    - "[SOURCE: sessão {id}, {project}] '{citação verbatim 2}'"
\```

## Decision Tree

\```javascript
IF ({condição_principal})
  STEP_1: {ação inicial — ex: STOP, ANALYZE}
  STEP_2: {avaliação de subcondições}
    IF ({subcondição_tipo_a}) → {ação_especializada_a}
    ELSE IF ({subcondição_tipo_b}) → {ação_especializada_b}
    ELSE → {ação_padrão_fallback}
\```

## Failure Modes

### {Nome Criativo do Incidente (ex: O Schema que Conflitou)}
- **Trigger:** {condição prática que causou a falha no histórico}
- **Manifestation:** {como a falha se manifestou em log, erro ou UI}
- **Detection:** {como farejar este problema o mais cedo possível}
- **Prevention:** {a mudança exata de paradigma para nunca mais repetir}
\```
```

### Numeração (com proteção de race condition — Gap #4)

```bash
# Pegar último ID
last=$(ls squads/squad-creator-pro/minds/oalanicolas/heuristics/AN_KE_*.md 2>/dev/null | sort | tail -1 | grep -oE '[0-9]+')
last=${last:-0}
next=$((last + 1))
target="squads/squad-creator-pro/minds/oalanicolas/heuristics/AN_KE_$(printf '%03d' $next).md"

# SAFETY: verificar se arquivo já existe (race condition protection)
while [[ -f "$target" ]]; do
  next=$((next + 1))
  target="squads/squad-creator-pro/minds/oalanicolas/heuristics/AN_KE_$(printf '%03d' $next).md"
done

echo "Próximo ID: AN_KE_$(printf '%03d' $next)"
```

**Anti-pattern:** NUNCA sobrescrever heurística existente. Se ID conflita, incrementar até achar slot vazio.

### Localização

```
squads/squad-creator-pro/minds/oalanicolas/heuristics/AN_KE_NNN.md
```

---

## Phase 5: PERSIST — Memory + Commit (2 min)

**Executor:** @oalanicolas
**Input:** Arquivos criados + decision cards atualizados
**Output:** Memory atualizado, commit pushed

### Step 5a: Memory Routing (Gap #2)

Atualizar o MEMORY.md do **projeto** (cross-session recall):

```bash
# Path: ~/.claude/projects/{project-slug}/memory/MEMORY.md
# Formato: uma linha por batch de heurísticas
echo "- [Heuristics AN_KE_NNN-NNN](file.md) — one-line description" >> MEMORY.md
```

**Regras de routing:**
- **SEMPRE** atualizar project memory (`~/.claude/projects/.../memory/MEMORY.md`)
- **SE** heurística existente em memory → atualizar entrada, não duplicar
- **NÃO** criar entries separadas por heurística — agrupar por sessão

### Step 5b: Commit + Push

```
feat(minds): add AN_KE_NNN-NNN {descrição} heuristics to @oalanicolas
```

### Step 5c: Token Update (se aplicável)

Se uma heurística define um novo threshold ou comportamento que pode virar token:

```yaml
- token_id: "TKN-NEW-THR-001"
  family: Threshold
  name: min_consumers_for_extraction
  value: 3
  description: "Extraído de AN_KE_013"
```

---

## Quality Check

| # | Check | Token | Weight |
|---|-------|-------|--------|
| 1 | Todas heurísticas têm [SOURCE:] rastreável | TKN-ESH-THR-001 | BLOCKER |
| 2 | Zero heurísticas genéricas (sem evidência específica) | TKN-ESH-THR-003 | BLOCKER |
| 3 | Zero duplicatas (overlap = atualizar, não criar) | TKN-ESH-BEH-001 | HIGH |
| 4 | Classificação Pareto ao Cubo aplicada | TKN-ESH-TAX-002 | HIGH |
| 5 | Formato padrão seguido (YAML + decision tree + evidence) | — | MEDIUM |
| 6 | Numeração contínua (sem gaps, sem sobreposição) | — | LOW |

**Score mínimo:** TKN-ESH-THR-004 = 5/6 (BLOCKER + HIGH devem passar)

---

## Composition Map

```yaml
process:
  id: "SP-EXTRACT-SESSION-HEURISTICS"
  mode: VALIDAR
  executor: "@oalanicolas"
  trigger: "*extract-session-heuristics"

  phases:
    - phase: 1
      name: "IDENTIFY"
      executor: "@oalanicolas"
      input: [session_context, handoff_file]
      output: [candidatas_brutas]
      checkpoint: "candidatas >= 5"
      duration: "5 min"

    - phase: 2
      name: "FILTER"
      executor: "@oalanicolas"
      input: [candidatas_brutas]
      output: [candidatas_filtradas, classification_pareto]
      checkpoint: "generico_ratio <= 30%"
      duration: "3 min"

    - phase: 3
      name: "OVERLAP"
      executor: "@oalanicolas"
      input: [candidatas_filtradas, existing_heuristics]
      output: [dedup_result, new_list, update_list]
      checkpoint: null
      duration: "3 min"

    - phase: 4
      name: "FORMALIZE"
      executor: "@oalanicolas"
      input: [new_list, update_list]
      output: [heuristics_files]
      checkpoint: "all have [SOURCE:]"
      duration: "4 min"

    - phase: 5
      name: "PERSIST"
      executor: "@oalanicolas"
      input: [heuristics_files]
      output: [memory_update, commit]
      checkpoint: "quality_check >= 5/6"
      duration: "2 min"

  tokens_produced:
    - "Novos tokens se thresholds/comportamentos emergirem das heurísticas"

  tokens_consumed:
    - TKN-ESH-THR-001 (source traceability)
    - TKN-ESH-THR-002 (min candidatas)
    - TKN-ESH-THR-003 (max genérico ratio)
    - TKN-ESH-THR-004 (quality check score)
    - TKN-ESH-BEH-001 (overlap action)
    - TKN-ESH-BEH-002 (triangulation promotion)
    - TKN-ESH-TAX-001 (heuristic types)
    - TKN-ESH-TAX-002 (pareto zones)
    - TKN-ESH-ACC-001 (accountability)
```

---

## Activation

Mission router do agente @oalanicolas:

```yaml
"*extract-session-heuristics":
  task: "tasks/an-extract-session-heuristics.md"
  data: null
```

**Invocação:** `*extract-session-heuristics`

---

*"Curadoria > Volume. Heurísticas de sessão são ouro — extraídas de execução real, não de livro."* 🧠
