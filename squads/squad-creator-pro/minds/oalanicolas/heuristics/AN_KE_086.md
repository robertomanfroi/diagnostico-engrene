# AN_KE_086 - Verify State Before Mutating
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: 97 instâncias de "antes de" em 5 meses de history — padrão cross-project massivo]

## Purpose

O padrão mais repetido de Alan: VERIFICAR o estado atual ANTES de qualquer mutação. Não assumir — confirmar. Schema pode já ter sido migrado. Seeds podem já ter sido aplicadas. Código pode já ter sido alterado. Verificar primeiro = evitar 80% dos erros.

## Configuration

```yaml
AN_KE_086:
  name: "Verify State Before Mutating"
  zone: "genialidade"
  trigger: "Qualquer operação que muda estado: migration, seed, deploy, refactor, delete."

  rule: |
    SE vai mutar estado (DB, arquivo, config, deploy)
    ENTÃO VERIFICAR estado atual PRIMEIRO.
    "Conferiu todo schema antes de criar esse migration?"
    Não assumir — confirmar. Verificação custa segundos. Rollback custa horas.

  veto_condition:
    trigger: "Executar migration/seed/delete sem verificar estado atual."
    action: "VETO — Confira primeiro. SELECT antes de ALTER. ls antes de rm. git status antes de commit."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents) vs State Verification Serialization"
    resolution: "Verificação prévia (segundos) é 10x mais rápido que rollback (horas). O padrão favora segurança porque o custo real da pressa > custo real da cautela."

  evidence:
    - "[SOURCE: 97 instâncias] 'antes de' aparece 97x no history como prerequisite gate"
    - "[SOURCE: sessão mmos e2c20669] 'confira no banco o que temos antes de continuar'"
    - "[SOURCE: sessão mmos 3ec2ae94] 'Conferiu todo schema antes de criar esse migration? isso ai cria o que? pq user_profiles a tabela já existe'"
    - "[SOURCE: sessão mmos a8145c99] 'antes de fazer uma migração precisamos entender conceitualmente como vamos aplicar os tiers'"
    - "[SOURCE: sessão mmos 017a1f24] 'calma vamos planejar antes de alterar qualquer coisa' (repetido 2x)"
```

## Decision Tree

```javascript
IF (about_to_mutate_state)
  STEP_1: VERIFY current state
    IF (database) → SELECT/DESCRIBE before ALTER/INSERT
    IF (files) → ls/cat before rm/mv/write
    IF (git) → git status/diff before commit/push
    IF (config) → read current before overwrite
  STEP_2: COMPARE expected vs actual
    IF (state_matches_expectation) → PROCEED
    IF (state_differs) → INVESTIGATE before acting
  NEVER: assume state from memory or prior session
```

## Failure Modes

### A Migration que Falha na Segunda Vez
- **Trigger:** ALTER TABLE RENAME sem verificar que coluna já foi renomeada.
- **Manifestation:** "column 'nome_clone' does not exist" — SQLSTATE 42703.
- **Detection:** Migration falha imediatamente.
- **Recovery:** Adicionar IF EXISTS guards (AN_KE_051).
- **Prevention:** SELECT column_name FROM information_schema ANTES de ALTER.

## Validation

**✓ Paradoxo Identificado:** Speed vs Safety — A tensão entre agir rápido e verificar antes de mutar.

**✓ Resolução:** O padrão resolve o paradoxo porque verificação prévia (5-10 segundos) é dramaticamente mais rápido que debug + rollback + reapply (2-4 horas). O custo real da pressa (risco de falha em produção) > custo real da cautela (segundos de espera).

**✓ Aplicabilidade:** Validado por 97 instâncias de "antes de" como gate em 5 meses de história. Padrão massivo cross-project — parte da DNA operacional de Alan.
