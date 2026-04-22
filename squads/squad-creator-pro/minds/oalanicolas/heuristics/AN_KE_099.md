# AN_KE_099 - CLAUDE.md as Living Config
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: 7+ instâncias cross-project (mentelendaria, mmos, sinkra-hub) — salve/adicione no CLAUDE.md]

## Purpose

Meta-heurística: CLAUDE.md (e equivalentes AGENTS.md, GEMINI.md) NÃO é documentação — é CONFIG VIVA do agente. Mas a evidence revela algo mais sutil que "salve tudo": Alan trata o arquivo com DISCIPLINA de engenharia — confere regras existentes antes de adicionar ("eu já tenho algumas regras no claude.md confira todas elas"), pede síntese e compactação ("se tivesse que sintetizar em apenas mais 3 quais deveriam ser?"), e exige que só o essencial entre ("colocar só o essencial dentro de claude.md"). Não é dump de regras — é curadoria ativa de config com pressão constante contra bloat.

## Configuration

```yaml
AN_KE_099:
  name: "CLAUDE.md as Living Config"
  zone: "excelencia"
  trigger: "Descoberta de regra/padrão durante sessão, OU revisão do arquivo de config do agente."
  sys_tension:
    tension_with: "AN_KE_038 (Gap de Reasoning = Processo Vago)"
    resolution: "Salve immediato (persistence), mas SEMPRE leia+sintetize+comprima (curation). Paradoxo resolvido via audit periódico: regras persistem, bloat não."

  rule: |
    SE descobriu regra/padrão/constraint durante sessão
    ENTÃO avaliar se é persistente (cross-session) ou efêmera (este task).
    SE persistente:
      (1) LER config atual PRIMEIRO — conferir se já existe regra similar
      (2) SINTETIZAR nova regra na menor forma possível
      (3) SALVAR imediatamente — "later" = never
    SE efêmera → NÃO pollute o config — manter em contexto da task
    MANUTENÇÃO: periodicamente auditar e comprimir regras (só essencial).

  veto_condition:
    trigger: "Sessão terminando com regra persistente não salva, OU adição de regra sem conferir existentes."
    action: "VETO — 'eu já tenho algumas regras no claude.md confira todas elas.' Leia antes de adicionar. Sintetize."

  evidence:
    - "[SOURCE: sessão c0429238, mentelendaria] 'adicione no seu CLAUDE.MD jamais, NUNCA em hipotese alguma, assine algum documento como Claude'"
    - "[SOURCE: sessão a5d42042, mentelendaria] 'salve isso no seu Claude.md'"
    - "[SOURCE: sessão 017a1f24, mmos] 'vamos evitar usar em arquivos, v2, v3, isso está inclusive como regra em claude.md'"
    - "[SOURCE: sessão 55333ac6, mmos] 'eu já tenho algumas regras no claude.md confira todas elas'"
    - "[SOURCE: sessão dc677053, mmos] 'sim, concordo, e as outras regras precisamos documentar tb e colocar só o essencial dentro de claude.md'"
    - "[SOURCE: sessão d829ca37, mmos] 'Quais regras similares a estas já temos em claude.md? e se tivesse que sintetizar em apenas mais 3 quais deveriam ser adicionadas?'"
    - "[PATTERN] 7+ instâncias cross-project confirmam: CLAUDE.md = runtime config com disciplina de engenharia (ler, sintetizar, comprimir), não dump de regras"
```

## Decision Tree

```javascript
IF (rule_or_pattern_discovered_during_session)
  STEP_1: CLASSIFY persistence
    IF (applies cross-session, cross-project) → PERSISTENT → proceed
    IF (applies only to this task/sprint) → EPHEMERAL → do NOT add to config

  STEP_2: CHECK existing config FIRST
    READ: current CLAUDE.md / AGENTS.md / GEMINI.md
    SEARCH: similar rule already exists?
      IF (exact match) → SKIP, do not duplicate
      IF (partial match) → MERGE/STRENGTHEN existing rule
      IF (no match) → proceed to add

  STEP_3: SYNTHESIZE for minimal footprint
    FORMAT: clear rule statement, not prose
    LENGTH: 1-2 lines if possible ("se não cabe em 1 linha, não extraiu direito" — AN_KE_008)
    AUDIT: "quais regras similares a estas já temos? se tivesse que sintetizar em apenas mais 3?"

  STEP_4: SAVE immediately
    TIMING: DURING session, not "later" — later = never
    TARGET: whichever config file is active (CLAUDE.md, AGENTS.md, GEMINI.md)

  MAINTENANCE (periodic):
    AUDIT: ler todas as regras — remover redundantes
    COMPRESS: "colocar só o essencial"
    QUESTION: "se tivesse que sintetizar em apenas mais 3 quais deveriam ser?"

  NEVER: end session with unsaved persistent rule
  NEVER: add without reading existing rules first (causes bloat)
  RELATED: AN_KE_079 (Cross-Session Context), AN_KE_072 (doc rot applies to config too)
```

## Failure Modes

### O Config que Virou Dump
- **Trigger:** Every session adds 2-3 rules. After 20 sessions, CLAUDE.md has 60 rules — half redundant.
- **Manifestation:** AI confused by contradicting rules. Performance degrades.
- **Detection:** `wc -l CLAUDE.md` > 200 lines. Rules contradict each other.
- **Prevention:** Periodic audit: "se tivesse que sintetizar em apenas mais 3?" Compress. "colocar só o essencial."

## Validation

**Paradoxo Identificado:** "Salvar imediatamente (urgência de persistence)" VS "Conferir/sintetizar antes (disciplina contra bloat)"

**Resolução:** O paradoxo é falso. Alan não quer velocidade descontrolada — quer **velocidade com rigor**. O movimento é:
1. Encontra padrão → Classifica (persistente? efêmero?)
2. SE persistente → lê existentes PRIMEIRO (não é impulso, é check)
3. Sintetiza na forma mínima (NUNCA poliglota)
4. Salva NO MESMO TURNO (não procrastina)
5. Periodicamente: audita tudo, remove redundância, recomprime

Não há conflito entre "salvar logo" e "curar antes". São **fases sequenciais do mesmo ciclo**, não trade-offs. O "veto" só ocorre quando pula (2) ou (3).
