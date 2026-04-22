# AN_KE_068 - Zero DB Table Cloning
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão f0681f25, mmos — "nunca crie backups duplicando a tabela"]

## Purpose

Criar um backup de tabela via clonagem direta no próprio banco do Supabase (ex: `users_backup`, `posts_old`) soa prático, mas inevitavelmente gera lixo cumulativo (`DB Bloat`) e polui o schema. Essa prática prejudica a observabilidade de clientes, introduz risco de dados fantasma interagirem por acidente com políticas RLS, e confunde o mapeamento. Alan trata o banco de dados como um terreno limpo: a regra é exportar o backup (baixar dumps, arquivos SQL) para fora dele, mas jamais criar tabelas mortas de backup dentro da instância.

## Configuration

```yaml
AN_KE_068:
  name: "Zero DB Table Cloning"
  zone: "excelencia"
  trigger: "Quando solicitado para proteger dados antes de uma migração destrutiva, truncamento ou alteração estrutural pesada."

  sys_tension:
    tension_with: "AN_KE_093 (Backup Before Mutation) vs Zero DB Table Cloning"
    resolution: |
      Paradoxo: Migrações perigosas exigem proteção de dados (backup), mas duplicação de tabelas no DB polui o schema.
      Resolução: Externalizar backups — usar pg_dump/CSV export (fora do DB) ao invés de tabelas clonadas dentro da instância.
      Garantia: Dados são protegidos (download + armazenamento local/S3), schema permanece limpo (sem tabelas _backup, _old, etc).

  rule: |
    SE for necessário criar fallback/backup de uma tabela antes de modificações perigosas
    ENTÃO DEVE-SE fazer o DUMP da tabela (csv, pg_dump) e manter o arquivo local/armazenado.
    NUNCA em nenhuma hipótese crie cópias duplicadas da tabela dentro do banco de dados (ex: rename/clone da tabela).
    O schema do Supabase precisa se manter limpo, contendo APENAS as tabelas ativas em produção.

  veto_condition:
    trigger: "Agente emite query SQL do tipo: `CREATE TABLE users_backup AS SELECT * FROM users;`"
    action: "VETO — 'mas nUNCA jamais crie bckups duplicando a tabela no supabase'. Faça export."

  evidence:
    - "[SOURCE: sessão f0681f25, mmos] 'nunca crie backups no supabase, duplicando a tabela, baixe ela mas nUNCA jamais crie bckups duplicando a tabela no supabase, escreva isso até na sua... mas nao faça isso de novo'"
    - "[SOURCE: sessão mmos (imagem analisada)] '[Image #1] temos algumas tabelas que por algum motivo errado, ficaram versionadas como backup no supabase, delete elas e garanta que isso nunca mais...'"
```

## Decision Tree

```javascript
IF (risky_db_operation_requires_backup)
  STEP_1: CHOOSE BACKUP STRATEGY
    OPTION A: `pg_dump` into local .sql file (APPROVED)
    OPTION B: Export as .csv (APPROVED)
    OPTION C: Duplicate table natively `CREATE TABLE _backup` (STRICTLY FORBIDDEN)
  STEP_2: EXECUTE APPROVED BACKUP (Download data)
  STEP_3: PROCEED with risky DB operation on the original table
  STEP_4: VERIFY success (If failure, restore using the dump)
```

## Failure Modes

### O Bloat Invisível
- **Trigger:** Ao longo de 6 meses, 12 migrations perigosas geram tabelas de backup no schema público.
- **Manifestation:** Queries dinâmicas ou ferramentas de auto-schema puxam "12 tabelas" sem utilidade, interfaces do Supabase viram um cemitério de lixo (Users, Users_bak, Users_old_2025).
- **Detection:** Analisar Supabase Table Editor buscando nomes de tabela que contenham strings de suffix como `_back`, `_old`, `_bkp`.
- **Prevention:** Impedir taxativamente na própria lógica do agente de Data-Engineering.

## Validation

✓ **Paradox Identified:** Proteção de dados (backup obrigatório antes de alterações) vs. Higiene de schema (zero duplicatas dentro do DB).

✓ **Resolution Applied:** Externalizar backups via pg_dump/CSV para fora da instância — dados ficam protegidos, schema fica limpo.

✓ **Enforcement:** Veto explícito em `veto_condition` impede syntax patterns que criem tabelas clonadas (_backup, _old, etc).

✓ **Evidence-Backed:** Fundado em directive do MMOS (sessão f0681f25) — recorrente em análises de schema poluído.

**Status:** HEURÍSTICA VALIDADA — Resolvida tensão sistêmica sem comprometer proteção de dados.
