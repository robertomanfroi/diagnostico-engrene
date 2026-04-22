# AN_KE_109 - English-Only DB Schema (AI Defensive Design)
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 799322de, lovable migration — "colunas em portugues costumam gerar eerros de SQL"]

## Purpose

Enquanto copywriters amam a pátria mãe, a relação entre LLMs robustos abstratos e bancos de dados SQL exige linguística universal. Nomenclaturas como `tabela_carrinho`, ou colunas `data_criacao`, aumentam violentamente as taxas de alucinação de agentes que geram consultas parametrizadas internamente ou criam APIs. A regra isola o Banco de Dados como Nação Inglesa: todas as Tables, Views, RPCs, Enums e colunas DEVEM usar o inglês (`carts`, `created_at`). A localização (i18n) das palavras pertence somente ao Client UI em tempo de Render.

## Configuration

```yaml
AN_KE_109:
  name: "English-Only DB Schema (AI Defensive Design)"
  zone: "genialidade"
  trigger: "Desenhando Data Definition Languages (DDL), Models no Prisma ou schemas para migrações Supabase."

  rule: |
    SE gerando ou renomeando chaves no domínio de Persistent Storage ou Código Lógico
    ENTÃO DEVE estar estritamente em the English Language. (tabelas, colunas, enums, endpoints).
    NUNCA use aportuguesamentos em camadas lógicas, pois IAs alucinam JOINs em português ou fazem typo.

  veto_condition:
    trigger: "Agente cria um arquivo migration com `CREATE TABLE compras_do_usuario (codigo_rastreio UUID)`."
    action: "VETO — 'tem muitos elementos como todo banco de dados com tabelas , descricoes, colunas em portugues, que na minha expderiencia costumam gerar muitos eerros de SQL com IA e voce muito bem o porque'."

  evidence:
    - "[SOURCE: sessão 799322de, db-refactor] 'tem muitos elementos como todo banco de dados com tabelas , descricoes, colunas em portugues, que na minha expderiencia costumam gerar muitos eerros de SQL com IA e voce muito bem o porque'"

  sys_tension:
    tension_with: "AN_KE_022 (Format Follows Generator) — LLM generators need English schema safety vs Documentation layer requires PT-BR coherence"
    resolution: "DB Layer = English (schema immunity from LLM hallucination) | Documentation Layer = Portuguese (founder context, narrative coherence). Separation by layer eliminates contradiction."
```

## Decision Tree

```javascript
IF (defining_database_entities_or_type_definitions)
  STEP_1: FORCE english dictionaries.
    Reject: `usuario_id`, `data_compra`.
    Approve: `user_id`, `purchased_at`.
  STEP_2: CHECK existing schema conventions. IF mixing languages -> Normalize entirely to English.
  STEP_3: Ensure UI labels (Zod localization, React text) cleanly handle the Portuguese translations, cleanly detached from the Data Schema.
```

## Failure Modes

### Semantic SQL Hallucination
- **Trigger:** Agente Claude é acionado para puxar relacionamentos entre "Vendas Múltiplas" num banco português.
- **Manifestation:** O Agente alucina nomeando queries como `select * from sales` e a query crasha por 3 iterations seguidas (pois a table era `vendas_realizadas`). Consumo inútil de tokens lendo o schema toda santa iteração.
- **Prevention:** Inglês padronizado resolve auto-completar na raiz matemática dos Modelos 3.7.

---

## Validation

✅ **Paradox Identified:** English-only mandate in DB schema contradicts PT-BR documentation requirement (CLAUDE.md).

✅ **Resolved via Layering:** Database layer (schema, DDL, types) operates in English for LLM safety. Documentation layer (Markdown, comments, narrative) operates in Portuguese for founder coherence and strategic alignment.

✅ **Epistemic Confidence:** ALTA — validated against CLAUDE.md §5 (PT-BR Acentuação) and session 799322de evidence (LLM hallucination on Portuguese schema names).

✅ **System Tension:** Encoded in `sys_tension` as (tension_with, resolution) tuple per SINKRA epistemic standards.
