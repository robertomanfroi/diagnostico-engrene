# AN_KE_110 - Abstraction Funneling (Everything is an Artifact)
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão db270b2c, data architecture — "sao artifacts, sao artefatos criados com base em dados"]

## Purpose

Bancos de dados e file systems de ML tendem à poluição: criam-se caixas para Análises, Sínteses, Relatórios, Checklists e Resumos independentemente. Para o AIOX, dados mastigados por agentes são essencialmente uma mesma infraestrutura matemática. O funil de abstração atua aglomerando derivações sob uma entidade polimórfica (ex: `mind_artifacts`). Se a pipeline pegou "Raw Transcripts" e formou "Análise SWOT" -> é um artifact (type=swot). Isso preserva a tabela limpa e evita a refatoração diária do backend quando um novo formato de sumário é desejado.

## Configuration

```yaml
AN_KE_110:
  name: "Abstraction Funneling (Everything is an Artifact)"
  zone: "genialidade"
  trigger: "Modelagem de classes ou banco de dados armazenando saídas computacionais de IAs, relatórios, resumos ou perfis."

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — Polimorfismo centralizado vs Redução agressiva de camadas"
    resolution: "Polimorfismo com Validators rígidos — permite extensão de tipos (flex) mas rejeita schemas divergentes (governance). JSONB payload é o escape hatch, mas `artifact_type` ENUM é invariante."

  rule: |
    SE você desenha onde armazenar diferentes tipos de inteligência derivada
    ENTÃO centralize os esquemas usando Polimorfismo / Single Table Inheritance (ex: `mind_artifacts`).
    NUNCA adicione uma Tabela ou Folder Novo para cada "Sabor de Resumo" que o Agente lançar.
    Sínteses, frameworks, audits e plans são todos Artefatos com metadados diferentes.

  veto_condition:
    trigger: "Agente sugere criar tabela genérica de `summaries`, `analyses` e `action_plans` com chaves idênticas de UUID num Supabase vazio."
    action: "VETO — 'synthesis, analysis e artifacts sao a mesma coisa, sao artifacts, sao artefatos criados com base em dados reais, são sintases, mas vamos chamar de mind_artifacts tudo que for uma abstracao de dados reais'."

  evidence:
    - "[SOURCE: sessão db270b2c, db-architecture] 'synthesis, analysis e artifacts sao a mesma coisa, sao artifacts... vamos chamar de mind_artifacts tudo que for uma abstracao de dados reais para futuras abstracoes'"
```

## Decision Tree

```javascript
IF (evaluating_where_to_store_new_llm_outputs_or_research)
  STEP_1: IDENTIFY data origin. Is it RAW primary text OR a processed abstraction?
  STEP_2: IF (Processed Abstraction)
    -> ROUTE to global `mind_artifacts` (or universal equivalents).
    -> Add dimensionality via ENUM `artifact_type = 'swot' | 'summary' | 'persona'`.
  STEP_3: Enforce strict JSONB payload storage inside the artifact for dynamic extensions.
```

## Failure Modes

### Tabela Fragmentada Explosiva
- **Trigger:** Surge a necessidade de um Agente "Curador de Memes Psicográficos".
- **Manifestation:** O dev gasta 3 horas alterando RLS Policies, Prisma, Mappers de Node.js APENAS para criar a tabela "memes_psicograficos" que armazena os exatos mesmos atributos que "profiles_card" armazenava (ID, MindID, Content, CreatedAt).
- **Prevention:** Um único guardião de polimorfismo contendo `type: 'psicographic_meme'`.

## Validation

✓ **Paradoxo Identificado:** Centralização rígida (polimorfismo monolítico) vs. escalabilidade emergente (novos tipos ad-hoc).
✓ **Tensão Sistêmica:** Flexibilidade (permitir novos tipos) × Governança (rejeitar schemas divergentes).
✓ **Resolução:** ENUM tipo é contrato invariante; JSONB payload permite extensão sem migração.
✓ **Aplicabilidade:** Decisões de arquitetura de dados com múltiplos "sabores" de output computacional.
