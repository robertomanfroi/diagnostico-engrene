# AN_KE_093 - Backup Before Mutation
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos 22650c09, 13c09251 — backup pedido antes de operações destrutivas]

## Purpose

Antes de qualquer operação que muda dados em produção ou deleta artefatos, FAZER BACKUP. Alan pede isso explicitamente e se frustra quando a IA pula esse passo.

## Configuration

```yaml
AN_KE_093:
  name: "Backup Before Mutation"
  zone: "excelencia"
  trigger: "Operação destrutiva: delete, migration, seed, schema change, bulk update."
  sys_tension:
    tension_with: "AN_KE_051 (Idempotent Operations) — operações idempotentes não precisam backup; mutações irreversíveis exigem"
    resolution: "Pausar apenas em operações destrutivas; executar autonomamente em operações reversíveis. Backup é validação, não bloqueio."

  rule: |
    SE operação vai mudar/deletar dados que não são facilmente recuperáveis
    ENTÃO BACKUP primeiro. Perguntar ao humano se quer backup.
    No handoff pro próximo: "faça backup antes de qualquer alteração."

  veto_condition:
    trigger: "DELETE ou ALTER em produção sem backup prévio."
    action: "VETO — Backup first. pg_dump, git stash, ou cópia manual."

  evidence:
    - "[SOURCE: sessão 22650c09] 'vamos fazer um handoff e no próximo ja peça para fazer backup de tudo que tá lá antes de qualquer alteracao'"
    - "[SOURCE: sessão 13c09251, mmos] 'fez backup antes de deletar?'"
```

## Decision Tree

```javascript
IF (destructive_operation: DELETE, ALTER, MIGRATION, SEED, BULK_UPDATE)
  STEP_1: BACKUP before anything
    DB: pg_dump / supabase db dump / snapshot
    Files: git stash / git branch backup-{date}
    Config: copy current state to .bak
  STEP_2: VERIFY backup is accessible
    Can you restore from this backup? Test.
  STEP_3: EXECUTE destructive operation
  STEP_4: VERIFY result
    IF (result wrong) → RESTORE from backup
  HANDOFF: "faça backup antes de qualquer alteração"
```

## Failure Modes

### O DELETE sem Volta
- **Trigger:** IA executa `DELETE FROM` em produção sem backup.
- **Manifestation:** "fez backup antes de deletar?" — perguntado DEPOIS do delete.
- **Detection:** No pg_dump or snapshot before migration.
- **Prevention:** Backup is step 0 of ANY destructive operation. Handoff must include backup instruction.

## Validation

**Paradoxo Identificado:** Confiança (inference_autonomy) × Cautela (data_integrity). Alan quer que a IA execute de forma autônoma, mas exige validação preventiva em operações irreversíveis.

**Resolução:** Executar autonomamente em operações reversíveis (lint, build, feature branches). Pausar e validar apenas em DELETE, ALTER, MIGRATION, ou operações com dados históricos em produção. O backup é a ponte entre confiança e segurança.

**Checklist de Validação:**
- [ ] Operação é destrutiva? (DELETE, ALTER, DROP, TRUNCATE, seed destructivo)
- [ ] Dados são recuperáveis via git, pg_dump, ou snapshot?
- [ ] Backup foi solicitado explicitamente ou executado antes da operação?
- [ ] Restore foi testado para confirmar que o backup funciona?
- [ ] Handoff contém instrução clara sobre backup para próximo agente?
