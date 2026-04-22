# AN_KE_067 - Database as Single Source of Truth
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões 1c81f504, 90f678b7, 12b1daab — "use pgsql"]

## Purpose

A documentação local, pastas de `/outputs/` ou arquivos Markdown frequentemente dessincronizam com o que realmente está rodando em produção. Alan impõe que quando houver dúvida ou necessidade de verificação de schemas ou dados (especialmente contagem, existências e migrações), a consulta deve ser feita DIRETAMENTE no banco de dados. "Não confie na documentação". O banco é o arbítrio final da verdade; qualquer outra fonte é meramente uma projeção sujeita a estarem desatualizadas. 

## Configuration

```yaml
AN_KE_067:
  name: "Database as Single Source of Truth"
  zone: "excelencia"
  trigger: "Validando integridade de dados, conferindo estados de sincronização, verificando schema."

  rule: |
    SE você precisar validar se um dado existe, o schema em uso ou o status real de informações
    ENTÃO USE query direta no banco de dados (ex: via pgsql) para confirmar.
    NÃO confie puramente em documentos .md do projeto ou no conteúdo da pasta /outputs/.
    A diferença de estado ocorre rapidamente; só o banco de dados representa o real.

  sys_tension:
    tension_with: "AN_KE_072 (Code Over Documentation) — Documentação como Contrato vs. DB Operacional Real"
    conflict: "DB é verdade operacional, mas Documentação é contrato formal. Qual prevalece quando divergem?"
    resolution: "HIERARCHY: Operação urgente → DB verdade. Planejamento/Design → Documentação contrato. Reconciliar post-operação."

  veto_condition:
    trigger: "Agente afirma categoricamente que a tabela X é de uma forma só porque leu um README.md ou schema antigo na raiz do projeto."
    action: "VETO — 'não confie na documentação'. Valide no banco primeiro."

  evidence:
    - "[SOURCE: sessão 1c81f504, mmos] 'use pgsql para confeirr o banco nao confie na documentacao, pq o banco já mudou muito desde entao'"
    - "[SOURCE: sessão 12b1daab, Hackathon-Hub] 'Confira fazendo um SQL, direto no banco e revisanto todas tabelas'"
    - "[SOURCE: sessão 90f678b7, mmos] 'precisa conferir no banco de dados na verdade e nao na pasta output'"
```

## Decision Tree

```javascript
IF (agent_needs_to_verify_data_or_schema)
  STEP_1: LOCATE DB connection details
    IF (connection not available) → ASK HUMAN to grant access or run query
  STEP_2: EXECUTE SQL query directly on the live database
  STEP_3: COMPARE results with local documentation or /outputs/
    IF (conflict exists) → TRUST DB and update local documentation if needed
  STEP_4: APPLY logic based strictly on DB truth
```

## Failure Modes

### A Alucinação de Schema Desatualizado
- **Trigger:** Agente lê um arquivo `/docs/database.md` feito há 3 meses e tenta gerar migrations em cima de suposições erradas.
- **Manifestation:** "coluna referenciada não existe" ou conflitos de Foreign Keys durante Deploy/Migration run.
- **Detection:** Agente não pediu pra bater query em psql/supabase e prosseguiu só com base em leitura de markdown.
- **Prevention:** Uso rotineiro de CLI para investigar tabelas e schemas ao assumir tarefas de Data Engineer ou DB manipulação.

## Validation

✅ **Heurística validada por:**
1. **Operacional:** Query direta via `psql`, `supabase-cli`, ou dashboard web valida estado real imediato
2. **Contrato:** Documentação desatualizada é detectada quando diverge do estado DB; aciona reconciliação
3. **Paradoxo resolvido:** DB vence em urgência operacional; documentação vence em planejamento formal
4. **Rastreabilidade:** Mudanças DB sem update de docs são debt técnico — marcar para L2 refactor
5. **Teste:** Validar schema esperado antes de assumir dependências em migrações ou queries críticas
