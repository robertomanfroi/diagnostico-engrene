---
task-id: an-assess-sources-score
name: "Score, Prioritize & Generate Source Map"
version: 2.0.0
execution_type: Hybrid
model: Haiku
model_rationale: "Script handles all 25 checkpoints deterministically. LLM for interpretation, tier assignment, and output assembly."
haiku_eligible: true
worker_script: "scripts/assess-sources.sh"
estimated-time: 20 min
complexity: medium
note: "Merged from v1.0.0 score + prioritize + output (de-atomization). Pure data marshaling consolidated."

inputs:
  required:
    - raw_sources_list: "Lista catalogada de fontes (output de an-assess-sources-collect)"
  optional:
    - sources_dir: "Caminho para diretorio com fontes baixadas (para worker script)"
    - extraction_results: "Resultados de extracao ja completada (para feedback loop)"

outputs:
  primary:
    - source_assessment: "Source map YAML completo com checkpoints, tiers, recommendations e gaps"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-assess-sources-score
  task_name: Score, Prioritize & Generate Source Map
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Hybrid
  estimated_time: 20m
  domain: Operational
  input:
  - '{''raw_sources_list'': ''Lista catalogada de fontes (output de an-assess-sources-collect)''}'
  - '{''sources_dir'': ''Caminho para diretorio com fontes baixadas (para worker script)''}'
  - '{''extraction_results'': ''Resultados de extracao ja completada (para feedback loop)''}'
  output:
  - '{''source_assessment'': ''Source map YAML completo com checkpoints, tiers, recommendations
    e gaps''}'
  action_items:
  - Score 25 Binary Checkpoints across 5 dimensions
  - Calculate Tier mechanically and prioritize extraction order
  - Generate Source Map YAML with recommendations, gaps, and optional feedback loop
  acceptance_criteria:
  - Cada fonte avaliada com 25 checkpoints binarios
  - Worker script executado primeiro quando fontes locais existem
  - Scoring calibration aplicada (generous interpretation)
  - Regra especial de Evolucao aplicada corretamente
  - Media calculada para cada fonte
  - Tier calculado por media das 5 dimensoes para cada fonte
  - Special rules aplicadas mecanicamente (Crown Jewel detection)
  - Nenhum override subjetivo no tier (notas subjetivas em "notes:" apenas)
  - Prioridade de extracao definida e ordenada
  - Summary com contagens por tier
  - Source map YAML gerado com checkpoints detalhados para cada fonte
  - Recommendations geradas baseadas em gaps de scoring
  - Gaps identificados para busca de fontes adicionais
  - Post-Extraction Feedback Loop executado (se extracao ja foi feita)
  - Feedback loop usa apenas EVIDENCIA, nao opiniao
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Score, Prioritize & Generate Source Map

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-assess-sources-score` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@oalanicolas` |
| **Execution Type** | `Hybrid (Worker 80% + Agent 20%)` |

## Metadata

- **Parent Task:** `an-assess-sources` (orchestrator stub)
- **Sequence:** Phase 2 of 2
- **Previous Task:** `an-assess-sources-collect`
- **Next Task:** None (final output)

## Purpose

Avaliar cada fonte com 25 checkpoints binarios, calcular tier mecanicamente, ordenar por prioridade de extracao, e gerar o source map YAML final com recommendations e gap analysis.

## Prerequisites

- `an-assess-sources-collect` completed with `raw_sources_list`
- Sources available (local files or metadata for manual assessment)

## MANDATORY PREFLIGHT: Run Worker Script FIRST

```
EXECUTE FIRST -- when sources directory exists with downloaded files:

  bash squads/squad-creator-pro/scripts/assess-sources.sh <sources-dir> > /tmp/preflight-assess-sources.yaml

IF the command fails -> FIX the script error. Do NOT proceed manually.
IF the command succeeds -> READ /tmp/preflight-assess-sources.yaml. Use as baseline scores.

VETO: If sources are already downloaded as files, do NOT grep checkpoints yourself.
      The script scores all 25 checkpoints per source in <1s each.

      Your job is INTERPRETATION ONLY:
      - Add context the script cannot detect (e.g., source type, duration, URL)
      - Override scores where domain knowledge matters (e.g., D3 Atualidade for books)
      - Generate recommendations and gap analysis

NOTE: Script works on FILE content (grep patterns). For sources not yet downloaded
      or for evaluating metadata (URL, duration, type), use manual assessment.
```

## Scoring Calibration (CRITICAL)

```yaml
scoring_philosophy:
  principle: "SCORE O QUE EXISTE, nao o que falta"
  bias_correction: "Haiku tende a sub-pontuar. Compensar sendo generoso."
  evidence_rule: "Se existe evidencia, conta ponto. Gaps vao para recommendations."

  checkpoint_rules:
    - "PASS = evidence EXISTS (not perfect)"
    - "FAIL = evidence MISSING (not weak)"
    - "Partial = PASS (generous interpretation)"
    - "Duvida = PASS (benefit of the doubt)"
```

---

## Step 1: Score 25 Binary Checkpoints

### Dimensao 1 -- AUTENTICIDADE (5 checkpoints)

| # | Checkpoint | O que procurar | Passa se... |
|---|------------|----------------|-------------|
| 1 | Espontaneidade | Tom de voz, padrao de fala | Nao parece scripted/teleprompter |
| 2 | Vulnerabilidade | Admite erros, duvidas | Mostra pelo menos 1 momento de vulnerabilidade |
| 3 | Respostas dificeis | Responde perguntas incomodas | Nao desvia de perguntas challenging |
| 4 | Nuance presente | Muda de ideia, nuances | Mostra evolucao ou nuance, nao binario |
| 5 | Storytelling pessoal | Historias proprias | Conta experiencias de primeira mao |

**Score Autenticidade = count(passed) -> 0-5**

### Dimensao 2 -- PROFUNDIDADE (5 checkpoints)

| # | Checkpoint | O que procurar | Passa se... |
|---|------------|----------------|-------------|
| 1 | Porque explicado | Raciocinio por tras | Explica motivacao, nao so acao |
| 2 | Framework presente | Metodologia/modelo | Tem estrutura repetivel SE/ENTAO |
| 3 | Exemplos especificos | Cases com detalhes | Cita nomes, numeros, datas especificos |
| 4 | Trade-offs discutidos | Pros e contras | Mostra decisoes e o que sacrificou |
| 5 | Conexoes cross-domain | Liga ideias | Conecta conceitos de areas diferentes |

**Score Profundidade = count(passed) -> 0-5**

### Dimensao 3 -- ATUALIDADE (5 checkpoints)

| # | Checkpoint | O que procurar | Passa se... |
|---|------------|----------------|-------------|
| 1 | Recencia | Data de publicacao | Criado nos ultimos 3 anos (2023+) |
| 2 | Contexto atual | Referencias temporais | Menciona contexto relevante atual |
| 3 | Nao contradito | Posicoes posteriores | Nao contradiz declaracoes mais recentes da pessoa |
| 4 | Evolucao visivel | Mudanca de pensamento | Mostra amadurecimento vs OBRA ANTERIOR do autor |
| 5 | Aplicabilidade | Relevancia hoje | Conselho ainda funciona em 2026 |

**Score Atualidade = count(passed) -> 0-5**

**REGRA ESPECIAL -- Checkpoint "Evolucao":**

```yaml
evolucao_rule:
  definition: "Compara com OBRA ANTERIOR do mesmo autor, nao evolucao interna do texto"
  first_work_rule: "SE e a primeira obra conhecida do autor -> evolucao = FALSE (sem baseline)"
  examples:
    - "$100M Offers (primeiro livro) -> FALSE | $100M Leads (segundo) -> TRUE se mostra mudanca"
  rationale: "Evolucao requer COMPARACAO. Primeira obra = always FALSE (MECANICO)."
```

### Dimensao 4 -- UNICIDADE (5 checkpoints)

| # | Checkpoint | O que procurar | Passa se... |
|---|------------|----------------|-------------|
| 1 | Contra-mainstream | Posicao diferente | Contradiz "senso comum" do mercado |
| 2 | Vocabulario proprio | Termos unicos | Usa palavras/expressoes signature |
| 3 | Framework original | Modelo nao-copiado | Metodologia nao encontrada em outros |
| 4 | Insight contra-intuitivo | Surpresa fundamentada | Conclusao inesperada com logica solida |
| 5 | Perspectiva singular | Angulo unico | Abordagem que outros autores nao tem |

**Score Unicidade = count(passed) -> 0-5**

### Dimensao 5 -- COMPLETUDE (5 checkpoints)

| # | Checkpoint | O que procurar | Passa se... |
|---|------------|----------------|-------------|
| 1 | Playbook presente | Passo a passo | Tem instrucoes acionaveis (faca X, depois Y) |
| 2 | Framework presente | SE/ENTAO | Tem regras condicionais documentadas |
| 3 | Exemplos reais | Cases | Tem pelo menos 2 exemplos concretos |
| 4 | Edge cases | Excecoes | Discute quando NAO funciona |
| 5 | Profundidade adequada | Duracao/extensao | >30min video OU >10 paginas texto |

**Score Completude = count(passed) -> 0-5**

---

## Step 2: Calculate Tier & Prioritize

### Tier Calculation (MECHANICAL)

```yaml
tier_calculation:
  formula: "media = (A + P + At + U + C) / 5"

  thresholds:
    ouro:
      range: ">= 4.0"
      meaning: "Fonte premium - prioridade maxima de extracao"
      checkpoints_passed: "20+ de 25"

    mixed:
      range: "3.0 - 3.9"
      meaning: "Usar com cautela - complementar, nao base"
      checkpoints_passed: "15-19 de 25"

    bronze:
      range: "< 3.0"
      meaning: "Descartar como base - baixo ROI"
      checkpoints_passed: "<15 de 25"

  special_rules:
    - "SE Autenticidade < 3 -> BRONZE (independente do resto)"
    - "SE Profundidade = 5 AND Autenticidade >= 4 -> CROWN JEWEL"
    - "SE todas dimensoes >= 4 -> CROWN JEWEL"

  # ANTI-OVERRIDE RULE (CRITICAL)
  no_subjective_override:
    principle: "Tier classification e MECANICA, nao subjetiva"
    rule: |
      SE special_rules sao satisfeitas -> APLICAR tier automaticamente
      NUNCA fazer override com julgamentos como:
        - "e livro 3 de 3, menos original"
        - "e sintese, nao criacao"
        - "parece menos importante"

    examples:
      correto:
        - "Score 5/5/5/5/5 -> CROWN JEWEL (todas dimensoes >= 4)"
        - "Score 5/5/4/4/4 -> CROWN JEWEL (Profundidade=5 AND Autenticidade>=4)"
      incorreto:
        - "Score 5/5/5/5/5 -> OURO porque 'e livro 3'" # PROIBIDO
        - "Score 5/5/5/5/5 -> OURO porque 'e sintese'" # PROIBIDO

    enforcement: |
      APOS calcular scores, APLICAR special_rules mecanicamente.
      Tier e DETERMINADO pelos numeros, nao por interpretacao.
      Notas subjetivas vao em "notes:", nao afetam tier.
```

### Prioritize Sources by Extraction Value

Ordenar fontes OURO por valor de extracao:

```yaml
extraction_priority:
  crown_jewel:
    description: "0.8% - gera 51% do resultado"
    types:
      - "Entrevistas longas (>1h) com perguntas dificeis"
      - "Podcasts em formato conversacional profundo"
      - "Debates/discussoes com challengers"

  ouro:
    description: "4% - gera 33% do resultado"
    types:
      - "Comentarios respondendo perguntas reais de audiencia"
      - "Cases detalhados com analise de decisoes"
      - "Livros com metodologia propria"

  impacto:
    description: "20% - gera 16% do resultado"
    types:
      - "Stories espontaneos"
      - "Posts com insights especificos"
      - "Cursos (secoes de Q&A)"

  bronze:
    description: "80% - ELIMINAR"
    types:
      - "Conteudo scripted/promocional"
      - "Reposts/compilacoes de outros"
      - "Material datado sem insights unicos"
```

### Assign Extraction Priority Numbers

For each source, assign `extraction_priority: {1-n}` based on:
1. Crown Jewels first (ordered by completude score)
2. Ouro next (ordered by profundidade score)
3. Mixed last (ordered by autenticidade score)
4. Bronze excluded from extraction queue

---

## Step 3: Output & Feedback Loop

### Generate Source Map YAML

Assemble the final output combining all data:

```yaml
source_assessment:
  mind: "{nome}"
  version: "2.0"
  assessment_date: "{ISO date}"

  summary:
    total_sources: {n}
    crown_jewel: {n}
    ouro: {n}
    mixed: {n}
    bronze: {n}
    average_quality: {media das medias}

  sources:
    - name: "{fonte}"
      type: "{video|podcast|livro|post|curso|entrevista}"
      url: "{link se disponivel}"
      duration: "{duracao/paginas}"
      checkpoints:
        autenticidade: { espontaneidade: bool, vulnerabilidade: bool, respostas_dificeis: bool, nuance: bool, storytelling: bool, score: 0-5 }
        profundidade: { porque_explicado: bool, framework: bool, exemplos_especificos: bool, tradeoffs: bool, cross_domain: bool, score: 0-5 }
        atualidade: { recencia: bool, contexto_atual: bool, nao_contradito: bool, evolucao: bool, aplicabilidade: bool, score: 0-5 }
        unicidade: { contra_mainstream: bool, vocabulario_proprio: bool, framework_original: bool, insight_contraintuitivo: bool, perspectiva_singular: bool, score: 0-5 }
        completude: { playbook: bool, framework_presente: bool, exemplos_reais: bool, edge_cases: bool, profundidade_adequada: bool, score: 0-5 }
      media: {A+P+At+U+C / 5}
      tier: "crown_jewel|ouro|mixed|bronze"
      extraction_priority: {1-n}
      notes: "{observacoes especificas -- subjective notes go HERE}"

  recommendations:
    - action: "{acao recomendada}"
      priority: "urgente|alta|media"
      rationale: "{por que}"

  gaps_identified:
    - "{dimensao/aspecto que falta cobertura}"
```

### Generate Recommendations

Based on scoring gaps:
- Dimensions with average < 3.0 across all sources -> recommend acquiring new sources
- Single-source coverage for key frameworks -> recommend triangulation
- Missing source types (e.g., no long interviews) -> recommend specific acquisition

### Identify Gaps

Scan for systematic weaknesses:
- Dimensions consistently low across all sources
- Missing source types that would improve specific dimensions
- Temporal gaps (all sources from same period)

### Post-Extraction Tier Reassessment (Conditional)

**When to execute:** ONLY after completing extraction (extract-framework, extract-implicit) on at least 1 source.

**Purpose:** Findings from the 3 lenses (GAP Analysis, Inversions, Evasion Scan) can CHANGE a source tier classification. Initial assessment is surface-level. Post-extraction provides deep evidence.

```yaml
tier_feedback_loop:
  upgrade_triggers:
    to_crown_jewel:
      - "GAP alto + >=2 inversoes reais com [SOURCE:] -> fonte tem pensamento ao vivo excepcional"
      - "Evasion Scan revela padrao unico (expert evade tema que TODOS no campo abordam) -> perspectiva singular"
    to_ouro:
      - "Fonte classificada MIXED mas GAP Analysis revelou desvios espontaneos com frameworks ocultos"
      - "Inversao encontrada em fonte que parecia generica -> reclassificar"

  downgrade_triggers:
    to_bronze:
      - "GAP baixo (zero desvios) + zero inversoes -> fonte e script, nao pensamento"
      - "Evasion Scan mostra evasao em temas CENTRAIS do expertise declarado -> fonte superficial"
    to_mixed:
      - "Fonte OURO mas Evasion Scan mostra evasao em >50% dos temas profundos -> confianca limitada"

  rules:
    - "Reclassificacao requer EVIDENCIA documentada com [SOURCE:]"
    - "NAO e override subjetivo -- e atualizacao baseada em dados novos"
    - "Documentar ANTES e DEPOIS no source map com justificativa"
    - "Reclassificacao pode mudar prioridade de extracao das fontes restantes"

  template:
    source: "{nome da fonte}"
    tier_original: "{ouro/mixed/bronze}"
    tier_reassessed: "{novo tier}"
    trigger: "{qual trigger ativou}"
    evidence: "{dados da lente que justificam}"
    impact: "{mudou prioridade de extracao? como?}"
```

#### Checkpoint: Feedback Loop vs Override

```yaml
checkpoint_feedback_loop:
  consult: "VALUES.clareza_radical"
  question: "Reclassificacao e baseada em EVIDENCIA das lentes ou em OPINIAO pos-hoc?"
  if_evidencia: "Reclassificar e documentar no source map"
  if_opiniao: "VETO -- manter tier original. Opiniao nao sobrescreve mecanica."
  rationale: "O feedback loop existe para incorporar DADOS NOVOS, nao para reinterpretar dados antigos."
```

---

## Acceptance Criteria

- [ ] Cada fonte avaliada com 25 checkpoints binarios
- [ ] Worker script executado primeiro quando fontes locais existem
- [ ] Scoring calibration aplicada (generous interpretation)
- [ ] Regra especial de Evolucao aplicada corretamente
- [ ] Media calculada para cada fonte
- [ ] Tier calculado por media das 5 dimensoes para cada fonte
- [ ] Special rules aplicadas mecanicamente (Crown Jewel detection)
- [ ] Nenhum override subjetivo no tier (notas subjetivas em "notes:" apenas)
- [ ] Prioridade de extracao definida e ordenada
- [ ] Summary com contagens por tier
- [ ] Source map YAML gerado com checkpoints detalhados para cada fonte
- [ ] Recommendations geradas baseadas em gaps de scoring
- [ ] Gaps identificados para busca de fontes adicionais
- [ ] Post-Extraction Feedback Loop executado (se extracao ja foi feita)
- [ ] Feedback loop usa apenas EVIDENCIA, nao opiniao

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AS-003 | Worker script available but not executed first | BLOCK -- run script |
| VETO-AS-004 | Subjective scoring override without evidence | BLOCK -- use checkpoint rules |
| VETO-AS-005 | Subjective override of mechanical tier | BLOCK -- tier is determined by numbers only |
| VETO-AS-006 | Crown Jewel criteria met but not applied | BLOCK -- apply special rules |
| VETO-AS-007 | Feedback loop reclassification without [SOURCE:] evidence | BLOCK -- evidence required |
| VETO-AS-008 | Opinion-based tier override in feedback loop | BLOCK -- keep original tier |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-assess-sources.md` | Parent orchestrator |
| `an-assess-sources-collect.md` | Previous phase (source collection) |
| `data/an-source-tiers.yaml` | Tier definitions reference |
| `an-extract-framework.md` | Extraction task (provides feedback loop data) |
| `extract-implicit.md` | Implicit extraction (provides feedback loop data) |
