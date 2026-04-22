# AN_KE_090 - Harvest Before Delete
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mmos 017a1f24 — revisão de agentes antes de migração]

**sys_tension:** (completeness_vs_speed, time_box_harvest_phase)

## Purpose

Antes de deletar artefatos obsoletos, COLHER o que tem de valor. Agentes antigos podem ter heurísticas, configs ou patterns que se perdem pra sempre no delete. Harvest first, then prune.

## Configuration

```yaml
AN_KE_090:
  name: "Harvest Before Delete"
  zone: "excelencia"
  trigger: "Deletando, arquivando, ou migrando artefatos que serão substituídos."

  rule: |
    SE vai deletar/arquivar artefatos (agentes, scripts, configs, docs)
    ENTÃO PRIMEIRO revisar e extrair o que tem valor.
    Deletar sem harvest = perder conhecimento irrecuperável.

  veto_condition:
    trigger: "rm -rf ou git rm batch sem revisão prévia do conteúdo."
    action: "VETO — Revise primeiro. Extraia patterns, configs, heurísticas. Depois delete."

  tension_with: "AN_KE_045 (Subtraction First Strategy) — Prioriza remover complexidade desnecessária rapidamente, criando atrito com harvest completo antes de delete"

  evidence:
    - "[SOURCE: sessão 017a1f24] 'Quero que revise o que dos agentes antigos talvez possamos aproveitar nos novos antes de deletarms eles e deixarmos tudo apenas com o sistema novo'"
    - "[SOURCE: sessão 13c09251, mmos] 'fez backup antes de deletar?'"
```

## Decision Tree

```javascript
IF (about_to_delete_or_archive)
  STEP_1: READ content before deleting
    FOR EACH artifact:
      SCAN: patterns, configs, heuristics, useful logic
      TAG: "harvest" or "safe to delete"
  STEP_2: HARVEST valuable content
    IF (patterns found) → extract to appropriate location
    IF (configs found) → merge into new system
    IF (heuristics found) → create AN_KE card
  STEP_3: BACKUP
    git stash / git branch archive-{date} / pg_dump
    VERIFY: backup is accessible
  STEP_4: DELETE
    ONLY after Steps 1-3 complete
  NEVER: rm -rf batch without reading first
```

## Failure Modes

### Os Agentes Antigos que Levaram Segredos
- **Trigger:** Migração para novo agent system. `rm -rf` old agents sem review.
- **Manifestation:** New agents missing patterns, configs, special prompts que existiam nos antigos.
- **Detection:** "cadê aquela config que tínhamos?" — após delete.
- **Prevention:** "revise o que dos agentes antigos talvez possamos aproveitar nos novos antes de deletarmos."

## Validation

**Paradoxo Identificado:** Harvest-Delete contém uma tensão irredutível entre **completeness** (colher tudo antes de deletar) e **speed** (terminar logo e liberar espaço). Quanto mais profundo o harvest, mais tempo leva; quanto mais rápido se executa, mais se perde.

**Resolução:** Aplicar time-boxing no harvest phase. Definir limite de tempo máximo (ex: 4h) para harvest e depois proceder com delete, aceitando que **não será 100% perfeito, mas terá sido validado e intencional**.

**Aplicação Prática:**
1. Set timer para 4 horas de harvest
2. Priorizar artefatos críticos (heurísticas, configs de negócio, patterns únicos)
3. Ao timeout, PARAR e prosseguir com delete
4. Documentar o que foi harvested vs. deixado para trás
5. Aceitar que alguns segredos ficarão perdidos — isso é o custo da transição
