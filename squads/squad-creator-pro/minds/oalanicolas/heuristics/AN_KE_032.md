# AN_KE_032 - Schema Immutability

**Type:** Infrastructure Security Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Supabase & Datastores
**Source:** [SOURCE: Extraído das orientações de governança estrita que impedem IAs e devs rápidos de renomear chaves que destruirão relações em cascade.]

## Purpose

Estabelecer uma zona vermelha de bloqueio para edições, droppings ou mutações estruturais em tabelas, stores e chaves centrais. Um erro de schema deleta o cérebro das automações. Nenhuma LLM pode ser confiada a "alterar um campo" se isso vazar pra dezenas de Workflows.

## Configuration

```yaml
AN_KE_032:
  name: "Schema Immutability"
  zone: "impacto"
  trigger: "Operações tocando DB, Types (TS), ou arquivos vitais como decision-cards.yaml e workspace root."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Paralelização máxima vs Bloqueio obrigatório de schema"
    resolution: "Dual-Gate: LLMs detectam necessidade de schema change, HITL aprova, LLM executa migration validada com rollback safety"

  rule: |
    SE a ação requer alterar a chave-primária virtual, estrutura de nomeação ou apagar campos base de um banco central
    ENTÃO BLOCK! Requeira Autorização Explícita Humana via Human In The Loop Handoff (HITL).

  veto_condition:
    trigger: "Modificações assíncronas em models.py ou supabse SQL schema sem aprovação de Alan."
    action: "VETO — Pause a fila e documente a modificação pretendida parando a execução."

  evidence:
    - "[EXACT WORDS]: O banco central, ou chaves globais, nunca devem ser tocados inadvertidamente sem o Human Gate explícito pois a reversão é complexa."
```

## Decision Tree

```javascript
IF (modifying_database_schema OR modifying_typescript_types OR global_hub_files)
  IF (human_approval_present == TRUE AND tests_confirm_deprecation_safety == TRUE)
    THEN ALLOW_MIGRATION
  ELSE
    THEN VETO
    THEN REQUEST_HUMAN_IN_THE_LOOP ("Alan, solicito permissão para injetar novo campo `is_verified` no Supabase users.")
```

## Failure Modes

### Cascade Data Annihilation
- **Trigger:** Atualizar uma foreign-key para um padrão mais moderno sem checar dependências transitórias em Node.js edges.
- **Manifestation:** Todos os squads da empresa perdem as chaves de rotas, quebrando a comunicação global e gerando pânico aos clientes por quebra de API.
- **Detection:** Log streams da Edge function apitando "Column does not exist".
- **Recovery:** Restore do DB do último log da meia noite.
- **Prevention:** Um gate inflexível que bloqueia mutações críticas em níveis operacionais autônomos.

## Integration with Workflow

```yaml
checkpoint:
  id: "schema-hitl"
  heuristic: AN_KE_032
  phase: "Database_Update"

  validation_questions:
    - "Existem mais de 3 consumidores lendo essa coluna que sofrerá alteração?"
    - "Foi documentado o impacto transversal antes de encabularmos a migration?"
```

## Validation

**Paradox Identified:** Automação vs Bloqueio Manual
- **Tension:** LLMs são esperadas executar workflows autonomamente, mas não podem ser confiadas a alterar schemas críticos
- **Resolution:** Implementar Dual-Gate — LLM detecta necessidade, submete para HITL, recebe aprovação, executa com safety gates (rollback, canary deploy, test suite)
- **Enforcement:** Toda migration em tabelas com >3 consumidores requer aprovação humana explícita antes da execução automatizada

**Checklist de Validação:**
- [ ] Schema change impacta mais de 3 consumidores? → Requer HITL
- [ ] Teste de rollback foi executado contra staging DB?
- [ ] Documentação de deprecation path foi criada?
- [ ] Edge functions foram atualizadas para nova estrutura?
