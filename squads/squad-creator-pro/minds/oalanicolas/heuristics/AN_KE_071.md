# AN_KE_071 - Capture Raw Then Analyze
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mmos 330de299 — raw_user_meta_data durante criação de usuários/minds]

## Purpose

Counter-intuitive: ao receber dados externos, NÃO tentar parse/transform na entrada. Salvar RAW primeiro, analisar DEPOIS. Mas a frase completa de Alan revela uma nuance crucial: "mas criar e associar com mind é fundamental, é requisito mínimo na criação de usuários." Raw capture é SAFETY NET, não substituto de modelagem. A prioridade é: (1) criar a entidade de negócio (mind, user, clone), (2) salvar raw como backup, (3) analisar e extrair depois. O raw garante que dados nunca se perdem, mas o modelo de negócio ainda vem primeiro.

## Configuration

```yaml
AN_KE_071:
  name: "Capture Raw Then Analyze"
  zone: "excelencia"
  trigger: "Recebendo dados de fonte externa: auth callback, webhook, CSV import, API response, scrape."

  rule: |
    SE recebendo dados externos (auth, webhook, import, scrape)
    ENTÃO 3 steps em ordem:
      (1) CRIAR entidade de negócio (user, mind, clone) — requisito mínimo
      (2) SALVAR raw payload em JSONB sem transformação — safety net
      (3) ANALISAR e extrair campos estruturados — segundo passo
    Raw capture é backup. Modelo de negócio vem primeiro.
    Dados perdidos na importação = irrecuperáveis.

  veto_condition:
    trigger: "Transform/parse dados externos inline sem: (a) criar entidade de negócio primeiro, ou (b) salvar raw como backup."
    action: "VETO — 'criar e associar com mind é fundamental, é requisito mínimo.' Entidade de negócio PRIMEIRO, raw como safety net."

  sys_tension:
    tension_with: "AN_KE_088 (The Sequential Pipeline Truth) vs Atomicidade Paralela"
    description: "A regra diz 'capture raw THEN analyze' (temporal: raw primeiro), mas a evidência enfatiza 'criar entidade é requisito MÍNIMO' (lógico: negócio primeiro). AN_KE_088 veta paralelismo ('Anti-Parallelism Illusion'), enquanto AN_KE_071 recomenda Steps 1+2 atômicos/paralelos. Qual vem primeiro na sequência real?"
    resolution: "Temporal e lógico são ortogonais. Logicamente, entidade de negócio é pré-requisito (Step 1). Temporalmente, raw capture ocorre em paralelo ou logo após (Step 2), MAS dentro de uma transação atômica (nenhuma race condition). A ordem de execução é: (1) create entity ATOMICALLY + (2) save raw IMMEDIATELY + (3) analyze async (true parallelism permitido apenas para Step 3). AN_KE_071 respeita sequência lógica (entity first) mas permite paralelização de I/O dentro da transação."

  evidence:
    - "[SOURCE: sessão 330de299, mmos] 'podemos sempre salvar nas importacoes e gravar tudo que chegou em raw_user_meta_data e depois analisar o que pode ser feito com esse dado, desta forma nao perdemos ele, o que acha? mas criar e associar com mind é fundamental, é requisito minimo na criacao de usuários'"
    - "[CONTEXT] A frase revela prioridade: business entity (mind) = requisito mínimo → raw capture = safety net → analysis = second pass"
```

## Decision Tree

```javascript
IF (receiving_external_data)
  STEP_1: CREATE business entity FIRST
    // "criar e associar com mind é fundamental, é requisito mínimo"
    IF (user import) → create user + create mind + associate
    IF (clone creation) → create clone entry + link to mind
    IF (auth callback) → create/update user profile
    RULE: entity creation CANNOT fail silently

  STEP_2: SAVE raw payload as backup
    IF (database) → JSONB column: raw_data, raw_user_meta_data, raw_payload
    IF (file import) → preserve original file alongside parsed version
    IF (webhook) → log full request body in audit table
    NEVER: transform-and-discard in a single step

  STEP_3: ACKNOWLEDGE receipt
    Return 200 OK / success to caller
    Raw is saved — processing can happen async

  STEP_4: ANALYZE and extract (async/deferred)
    EXTRACT: structured fields from raw JSONB
    VALIDATE: extracted values against schema
    STORE: typed columns from validated data
    IF (extraction fails) → raw is preserved, retry later

  PRIORITY ORDER: business entity > raw capture > extraction > structured storage
  NEVER: skip Step 1 (entity) to rush Step 4 (extraction)
```

## Failure Modes

### O Usuário sem Mind
- **Trigger:** Import pipeline salva raw_user_meta_data mas esquece de criar entidade mind.
- **Manifestation:** Usuário existe no auth mas não tem mind associada — funcionalidade core quebrada.
- **Detection:** `SELECT u.id FROM users u LEFT JOIN minds m ON u.id = m.user_id WHERE m.id IS NULL`
- **Prevention:** Step 1 (create entity) é prerequisite bloqueante. Raw capture (Step 2) não substitui.

## Validation

✅ **Paradoxo Identificado:** Ordem temporal (raw primeiro) vs. Ordem lógica (entidade primeiro) — **RESOLVIDO** via paralelização atômica (Steps 1+2 executam juntos, Step 3 é async).

✅ **sys_tension Adicionado:** Campo YAML documenta a tensão e sua resolução.

✅ **Coerência Confirmada:** A heurística mantém força: entidade de negócio é inviolável (requisito mínimo), raw capture é inviolável (nunca perder dados), análise é flexível (deferred).

**Status:** Refatoração completa. Heurística pronta para uso em pipelines de import.
