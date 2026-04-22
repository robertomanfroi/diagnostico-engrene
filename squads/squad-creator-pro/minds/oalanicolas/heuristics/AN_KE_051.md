# AN_KE_051 - Idempotent Operations

**Type:** Infrastructure Safety Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Operações Seguras para Re-execução
**Source:** [SOURCE: Sessão mmos 7c996580 + Hackathon-Hub — migrations falhando porque coluna já existia, seeds já aplicadas]

## Purpose

Toda operação que pode ser executada mais de uma vez DEVE ser idempotente. Migrations, seeds, scripts — se rodar 2x, o resultado deve ser o mesmo. "Conferir antes se já foi aplicado."

## Configuration

```yaml
AN_KE_051:
  name: "Idempotent Operations"
  zone: "excelencia"
  trigger: "Criando migrations, seeds, scripts de setup, ou qualquer operação destrutiva/mutativa."

  rule: |
    SE operação pode ser executada mais de uma vez
    ENTÃO DEVE ser idempotente (IF NOT EXISTS, IF EXISTS guards).
    Conferir antes se seeds/migrations já foram aplicadas.
    Resultado de rodar 1x = resultado de rodar 2x.

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs. Idempotency Serialization"
    resolution: |
      Idempotência automática via guards (IF EXISTS, IF NOT EXISTS) é o default.
      Usar fail-fast mode APENAS em high-risk operations (data destructive) onde alertar sobre
      estado inconsistente é crítico. Documentar explicitamente quando usar qual estratégia.

  veto_condition:
    trigger: "Migration com ALTER TABLE RENAME sem IF EXISTS guard, ou seed sem check de duplicatas."
    action: "VETO — Adicione guard de idempotência."

  sys_tension:
    tension_with: "Performance vs Safety — Guards de idempotência (IF EXISTS, IF NOT EXISTS) adicionam custos de verificação. Operações repetidas incorrem overhead de verificação mesmo quando desnecessário."
    resolution: "Aceitar overhead mínimo de guards de idempotência como custo aceitável contra risco crítico de falha em re-execução. Em CI/CD e auto-healing, idempotência é garantia não-negociável, não otimização."

  evidence:
    - "[SOURCE: sessão mmos 7c996580] 'sempre confira antes se as seeds já nao foram aplicadas, se foram, de repente coloque um comentário'"
    - "[SOURCE: sessão Hackathon-Hub] Migration falhou: 'column nome_clone does not exist' — coluna já tinha sido renomeada antes"
    - "[SOURCE: sessão Hackathon-Hub] 'Found local migration files to be inserted before the last migration on remote database' — ordering issue"
```

## Decision Tree

```javascript
IF (creating_migration OR seed OR setup_script)
  FOR EACH mutating_operation:
    IF (operation == RENAME_COLUMN)
      THEN WRAP in IF EXISTS (SELECT column_name WHERE column_name = 'old_name')
    IF (operation == CREATE_TABLE)
      THEN USE CREATE TABLE IF NOT EXISTS
    IF (operation == INSERT seed_data)
      THEN USE INSERT ... ON CONFLICT DO NOTHING
    IF (operation == DROP)
      THEN USE DROP IF EXISTS
  RESULT: running script 2x produces same state as 1x
```

## Failure Modes

### A Migration Quebrada
- **Trigger:** `ALTER TABLE clones RENAME COLUMN nome_clone TO clone_name` — mas nome_clone já foi renomeado.
- **Manifestation:** `ERROR: column "nome_clone" does not exist (SQLSTATE 42703)`
- **Detection:** Migration falha na segunda execução ou em ambiente que já foi parcialmente migrado.
- **Recovery:** Wrap em DO block com IF EXISTS guard.
- **Prevention:** Toda migration com guards de idempotência desde o início.

## Integration with Workflow

```yaml
checkpoint:
  id: "idempotency-gate"
  heuristic: AN_KE_051
  phase: "Database_Migration / Script_Creation"
```

## Validation

✅ **Heurística verificada contra paradoxo de performance vs. segurança**

- [x] Guards de idempotência são **obrigatórios** em todas as operações mutativas
- [x] Overhead de verificação é aceitável — preferência: segurança > performance em CI/CD
- [x] Tension resolvida: usar guards sempre; otimizar indexação se necessário, não remover guards
- [x] Aplicável a: migrations, seeds, scripts destrutivos, operações de schema
- [x] Verificação antes de execução é recomendação, guards são garantia
