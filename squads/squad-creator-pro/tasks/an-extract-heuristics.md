---
task-id: an-extract-heuristics
name: "Extrair Heurísticas de Expert (Fontes Externas)"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Requer síntese profunda de padrões de decisão implícitos em fontes diversas — Opus para profundidade"
estimated-time: 20-40 min
complexity: medium-high
agent: "@oalanicolas"
process_id: "SP-EXTRACT-HEURISTICS"
mode: CRIAR

inputs:
  required:
    - expert_name: "Nome do expert cujas heurísticas serão extraídas"
    - sources: "Fontes classificadas (ouro/bronze) — output de *assess-sources ou lista manual"
  optional:
    - domain: "Área de expertise (copy, legal, marketing, etc)"
    - target_depth: "shallow (5-10 heurísticas) | deep (15-30 heurísticas)"
    - existing_extraction: "Path para extração prévia (Voice/Thinking DNA) se houver"
    - focus_areas: "Categorias específicas para focar (ex: pricing, negotiation)"

outputs:
  primary:
    - heuristics_yaml: "Bloco YAML com heurísticas formatadas (SE/ENTÃO/NUNCA)"
    - decision_cards: "Entries prontas para decision-cards.yaml (L2)"
    - heuristic_files: "Arquivos .md individuais no formato L3 (se persist=true)"
  secondary:
    - source_map: "Mapa de rastreabilidade heurística → fonte"
    - gap_report: "Áreas do expert sem heurísticas extraíveis (evidência insuficiente)"

extensions:
  - task_id: an-extract-session-heuristics
    relationship: "specialization"
    description: "Especialização para sessões de trabalho (execução real vs fontes externas)"

checklist: "checklists/heuristic-extraction.md"
template: "templates/session-heuristic-tmpl.md"
elicit: false
---

# SP-EXTRACT-HEURISTICS — Extração de Heurísticas de Expert

> **Framework base de extração de heurísticas.** Extrai regras de decisão (SE/ENTÃO),
> vetos, e padrões de julgamento de fontes externas: livros, entrevistas, podcasts,
> transcripts, artigos, cases reais.
>
> **Diferença do extract-session-heuristics:** Esta extrai de **experts** (pessoas, fontes).
> A session-heuristics extrai de **sessões de execução** (o que aprendemos fazendo).
>
> **Princípio:** "Heurísticas são o DNA operacional. Framework sem heurística = teoria.
> Heurística sem [SOURCE:] = opinião."

---

## Process Tokens

```yaml
tokens:
  - token_id: "TKN-EXH-THR-001"
    family: Threshold
    name: min_source_traceability
    value: 100
    unit: "%"
    description: "Todas as heurísticas DEVEM ter [SOURCE:]. Zero tolerância."
    consumed_by: ["phase_4_formalize", "quality_check"]

  - token_id: "TKN-EXH-THR-002"
    family: Threshold
    name: min_candidatas_brutas
    value: 8
    description: "Mínimo de candidatas brutas antes de filtrar. Se < 8, fontes insuficientes."
    consumed_by: ["phase_1_scan"]

  - token_id: "TKN-EXH-THR-003"
    family: Threshold
    name: max_generico_ratio
    value: 25
    unit: "%"
    description: "Se > 25% das candidatas são genéricas (💩), varredura está rasa. Threshold mais rigoroso que session (30%) porque fontes externas têm mais profundidade disponível."
    consumed_by: ["phase_2_filter"]

  - token_id: "TKN-EXH-THR-004"
    family: Threshold
    name: min_quality_check_score
    value: 6
    unit: "de 7"
    description: "Score mínimo no quality check para aprovar extração."
    consumed_by: ["quality_check"]

  - token_id: "TKN-EXH-THR-005"
    family: Threshold
    name: min_ouro_sources
    value: 60
    unit: "%"
    description: "Mínimo 60% das fontes usadas devem ser OURO. Bronze = ruído."
    consumed_by: ["phase_0_gate"]

  - token_id: "TKN-EXH-BEH-001"
    family: Behavior
    name: triangulation_required
    value: true
    description: "Heurísticas com confiança ALTA requerem 2+ fontes independentes confirmando."
    consumed_by: ["phase_3_validate"]

  - token_id: "TKN-EXH-BEH-002"
    family: Behavior
    name: inference_marking
    value: "mandatory"
    description: "Conceito inferido sem citação direta → [INFERRED] obrigatório. Nunca apresentar inferência como fato."
    consumed_by: ["phase_4_formalize"]

  - token_id: "TKN-EXH-TAX-001"
    family: Taxonomy
    name: heuristic_types
    value: ["Decision Heuristic", "Veto Heuristic", "Prioritization Heuristic", "Diagnostic Heuristic", "Timing Heuristic", "Risk Heuristic"]
    description: "Tipos válidos de heurística de expert. Inclui tipos adicionais vs session (Timing, Risk, Diagnostic)."
    consumed_by: ["phase_4_formalize"]

  - token_id: "TKN-EXH-TAX-002"
    family: Taxonomy
    name: pareto_zones
    value:
      genialidade: "0.8% — muda paradigma, contraintuitivo, comprovado"
      excelencia: "4% — guardrail que previne erro caro"
      impacto: "20% — boa prática que acelera"
      merda: "80% — genérico, qualquer expert diria, descartar"
    description: "Classificação obrigatória via Pareto ao Cubo."
    consumed_by: ["phase_2_filter"]

  - token_id: "TKN-EXH-ACC-001"
    family: Accountability
    name: extractor
    value: "@oalanicolas"
    description: "Knowledge Architect é accountable pela qualidade da extração."
    consumed_by: ["all_phases"]
```

---

## Phase 0: SOURCE GATE — Validação de Fontes (2 min)

**Executor:** @oalanicolas
**Input:** sources (lista de fontes)
**Output:** fontes_aprovadas, fontes_rejeitadas

Antes de extrair qualquer coisa, validar que as fontes são de qualidade suficiente.

### Checklist de Gate

```yaml
source_gate:
  checks:
    - "Fontes classificadas como OURO ≥ 60%?"  # TKN-EXH-THR-005
    - "Pelo menos 1 fonte primária (entrevista, livro do expert, Q&A)?"
    - "Fontes cobrem 2+ contextos diferentes do expert?"
    - "Nenhuma fonte é exclusivamente conteúdo de terceiros sobre o expert?"
  pass: "Prosseguir para Phase 1"
  fail: "ABORT — buscar fontes melhores ou rodar *assess-sources primeiro"
```

### Classificação Rápida (se fontes não pré-classificadas)

| Tipo de Fonte | Classificação | Justificativa |
|---------------|---------------|---------------|
| Entrevista longa (30+ min) | 🥇 OURO | Pensamento espontâneo, perguntas profundas |
| Livro/artigo autoral | 🥇 OURO | Frameworks documentados pelo expert |
| Q&A / AMA / comentários | 🥇 OURO | Respostas diretas, sem script |
| Case study com números | 🥇 OURO | Decisões rastreáveis com outcome |
| Palestra/keynote | 🥈 PRATA | Estruturado mas autêntico |
| Podcast curto (<15 min) | 🥈 PRATA | Pouca profundidade, algum valor |
| Artigo de terceiro | 🥉 BRONZE | Interpretação, não fonte primária |
| Palestra antiga genérica | 🥉 BRONZE | Provavelmente reciclado |
| Resumo/compilação | 🥉 BRONZE | Perda de nuance |

---

## Phase 1: SCAN — Varredura de Heurísticas Candidatas (5-10 min)

**Executor:** @oalanicolas
**Input:** fontes_aprovadas, focus_areas (opcional)
**Output:** Lista de 8-30 candidatas brutas

### 6 Lentes de Extração

Para cada fonte OURO, aplicar as 6 lentes:

| Lente | Pergunta-Guia | O que Extrair |
|-------|---------------|---------------|
| **Decisão** | "Quando X acontece, o que o expert FAZ?" | Regras SE/ENTÃO |
| **Veto** | "O que o expert NUNCA faz? O que recusa?" | Regras de bloqueio |
| **Priorização** | "Entre A e B, o expert escolhe qual? Por quê?" | Hierarquia de valores |
| **Diagnóstico** | "Como o expert IDENTIFICA o problema?" | Patterns de reconhecimento |
| **Timing** | "QUANDO o expert age vs espera?" | Triggers temporais |
| **Risco** | "Onde o expert é cauteloso? Onde é agressivo?" | Risk profile |

### Perguntas de Extração (Critical Decision Method)

```
1. "Em que PONTO EXATO o expert decidiu X? O que mudou na situação?"
2. "O que o expert faz que OUTROS EXPERTS NO MESMO DOMÍNIO NÃO fazem?"
3. "Qual é a regra que o expert aplica que é CONTRAINTUITIVA?"
4. "Quando o expert RECUSA uma oportunidade aparentemente boa, qual é o critério?"
5. "Que METÁFORA ou ANALOGIA o expert usa para explicar decisões complexas?"
6. "Que ERRO o expert cometeu que gerou uma regra permanente?"
7. "Que SEQUÊNCIA o expert segue que outros pulam etapas?"
8. "Onde o expert DISCORDA do consenso do mercado?"
```

### Formato de Candidata Bruta

```yaml
- id: CAND-001
  source: "[SOURCE: {livro/entrevista}, {página/minuto}]"
  lente: "Decisão"
  raw_quote: "Citação direta ou paráfrase próxima"
  heuristic_draft: "SE {condição} → ENTÃO {ação}"
  confidence: "ALTA|MEDIA|BAIXA"
  contraintuitivo: true|false
```

### Checkpoint Phase 1

```yaml
gate: "candidatas >= TKN-EXH-THR-002 (8)"
pass: "Prosseguir para Phase 2"
fail: "Fontes insuficientes — buscar mais fontes OURO ou aprofundar leitura"
```

---

## Phase 2: FILTER — Pareto ao Cubo (3-5 min)

**Executor:** @oalanicolas
**Input:** Lista de candidatas brutas
**Output:** Lista filtrada com classificação por zona

### Classificação

| Zona | Critério | Ação | Emoji |
|------|----------|------|-------|
| **0,8% Genialidade** | Contraintuitivo + comprovado + único deste expert | FORMALIZAR primeiro | 🧠 |
| **4% Excelência** | Guardrail valioso que previne erro caro | FORMALIZAR | 💎 |
| **20% Impacto** | Boa prática com evidência + [SOURCE:] forte | FORMALIZAR se aprovado na validação | 🔥 |
| **80% Merda** | Qualquer expert diria isso, genérico, sem evidência específica | DESCARTAR | 💩 |

### Teste de Distintividade (anti-💩)

```
Pergunta 1: "200 experts neste domínio diriam a mesma coisa?"
  SE SIM → 💩 (genérico)
  SE NÃO → prosseguir

Pergunta 2: "Esta heurística tem CONTEXTO ESPECÍFICO de aplicação?"
  SE SIM → prosseguir
  SE NÃO → provavelmente genérica (💩)

Pergunta 3: "Tem OUTCOME DOCUMENTADO (números, caso real)?"
  SE SIM → 🔥 ou acima
  SE NÃO → avaliar com cuidado
```

### Checkpoint Phase 2

```yaml
gate: "generico_ratio <= TKN-EXH-THR-003 (25%)"
pass: "Prosseguir para Phase 3"
warn: "Re-analisar candidatas — usar lentes de extração mais profundas"
```

---

## Phase 3: VALIDATE — Triangulação + Confiança (3-5 min)

**Executor:** @oalanicolas
**Input:** Lista filtrada
**Output:** Lista validada com confidence levels

### Regras de Triangulação (TKN-EXH-BEH-001)

```yaml
triangulation_rules:
  ALTA:
    requirement: "2+ fontes INDEPENDENTES confirmam"
    format: "[SOURCE: fonte1] + [SOURCE: fonte2]"
    action: "Formalizar com confidence ALTA"

  MEDIA:
    requirement: "1 fonte forte + padrão consistente com outras heurísticas"
    format: "[SOURCE: fonte1] + [CONSISTENT_WITH: AN_KE_NNN]"
    action: "Formalizar com [MEDIA] tag"

  BAIXA:
    requirement: "1 menção isolada, sem corroboração"
    format: "[SOURCE: fonte1] + [INFERRED]"
    action: "Formalizar APENAS se contraintuitiva e com valor alto"
    veto: "SE genérica + BAIXA → DESCARTAR"
```

### Validação Cruzada

```
Para cada heurística:
1. Verificar: "Contradiz alguma heurística já extraída?"
   SE SIM → investigar qual está correta (contexto?)
2. Verificar: "Complementa heurística existente?"
   SE SIM → considerar merge ou hierarquia
3. Verificar: "Expert aplica EXCEÇÕES a esta regra?"
   SE SIM → documentar exceção como parte da heurística
```

---

## Phase 4: FORMALIZE — 3 Camadas (5-10 min)

**Executor:** @oalanicolas
**Input:** Lista validada
**Output:** Heurísticas formalizadas em L2 (YAML) + L3 (.md)

### Formato de Heurística Formalizada

Cada heurística segue o template `templates/session-heuristic-tmpl.md` com as seguintes adaptações para fontes externas:

#### L2 — Decision Card (YAML)

```yaml
- id: "{PREFIX}_KE_NNN"  # Prefixo baseado no expert (ex: NH para Naval, AH para Hormozi)
  name: "Nome descritivo"
  rule: "SE {condição} → ENTÃO {ação}"
  zone: "{genialidade|excelencia|impacto}"
  trigger: "{quando se aplica}"
  anti_pattern: "{o que acontece quando ignora}"
  evidence: "{dado empírico [SOURCE:]}"
  confidence: "ALTA|MEDIA"
  expert: "{nome do expert}"
```

#### L3 — Arquivo .md Completo

Seguir `templates/session-heuristic-tmpl.md` com campo **Source** apontando para a fonte externa:

```markdown
**Source:** [SOURCE: {Livro/Entrevista/Podcast}, {página/minuto/episódio}]
```

### Regras de Formalização

1. **Toda heurística DEVE ter [SOURCE:]** — TKN-EXH-THR-001
2. **Inferências marcadas [INFERRED]** — TKN-EXH-BEH-002
3. **Tipo válido** — TKN-EXH-TAX-001
4. **Zona Pareto classificada** — TKN-EXH-TAX-002
5. **SE/ENTÃO/NUNCA formato** — não aceitar descrições vagas

### Numeração

Prefixo baseado no expert + `_KE_` + número sequencial:

```
{INITIALS}_KE_001, {INITIALS}_KE_002, ...
```

Exemplos: `NH_KE_001` (Naval Heuristic), `AH_KE_001` (Alex Hormozi), `AN_KE_001` (Alan Nicolas)

---

## Phase 5: DELIVER — Output + Rastreabilidade (2 min)

**Executor:** @oalanicolas
**Input:** Heurísticas formalizadas
**Output:** Pacote completo para handoff ou uso direto

### Output Structure

```yaml
extraction_report:
  expert: "{nome}"
  domain: "{área}"
  sources_used: N
  sources_ouro: N
  candidatas_brutas: N
  descartadas_generico: N
  formalizadas: N
  by_zone:
    genialidade: N
    excelencia: N
    impacto: N
  by_type:
    decision: N
    veto: N
    prioritization: N
    diagnostic: N
    timing: N
    risk: N
  confidence_distribution:
    alta: N
    media: N
  gaps: ["áreas sem heurísticas extraíveis"]
```

### Source Map

```yaml
source_map:
  - heuristic_id: "{ID}"
    sources:
      - "[SOURCE: {ref1}]"
      - "[SOURCE: {ref2}]"
    confidence: "ALTA"
```

---

## Veto Conditions

| ID | Condition | Token | Action |
|----|-----------|-------|--------|
| VETO-EXH-001 | Heurística sem [SOURCE:] | TKN-EXH-THR-001 | BLOCK — adicionar fonte ou descartar |
| VETO-EXH-002 | Heurística genérica (200 experts diriam igual) | TKN-EXH-TAX-002 | BLOCK — não é heurística, é senso comum |
| VETO-EXH-003 | < 60% fontes OURO | TKN-EXH-THR-005 | BLOCK — buscar fontes melhores primeiro |
| VETO-EXH-004 | Inferência não marcada como [INFERRED] | TKN-EXH-BEH-002 | BLOCK — marcar ou encontrar fonte |
| VETO-EXH-005 | < 8 candidatas brutas | TKN-EXH-THR-002 | BLOCK — aprofundar varredura |
| VETO-EXH-006 | Heurística contradiz outra sem resolução | — | BLOCK — resolver contradição primeiro |

---

## Quality Check

| # | Check | Token | Weight |
|---|-------|-------|--------|
| 1 | Todas heurísticas têm [SOURCE:] rastreável | TKN-EXH-THR-001 | BLOCKER |
| 2 | Zero heurísticas genéricas passaram filtro | TKN-EXH-THR-003 | BLOCKER |
| 3 | Inferências marcadas [INFERRED] | TKN-EXH-BEH-002 | BLOCKER |
| 4 | Triangulação aplicada (2+ fontes para ALTA) | TKN-EXH-BEH-001 | HIGH |
| 5 | Classificação Pareto ao Cubo aplicada | TKN-EXH-TAX-002 | HIGH |
| 6 | Formato SE/ENTÃO/NUNCA seguido | — | HIGH |
| 7 | Source map completo | — | MEDIUM |

**Score mínimo:** TKN-EXH-THR-004 = 6/7 (todos BLOCKER + HIGH devem passar)

---

## Composition Map

```yaml
process:
  id: "SP-EXTRACT-HEURISTICS"
  mode: CRIAR
  executor: "@oalanicolas"
  trigger: "*extract-heuristics"

  phases:
    - phase: 0
      name: "SOURCE GATE"
      executor: "@oalanicolas"
      input: [sources]
      output: [fontes_aprovadas]
      checkpoint: "ouro_ratio >= 60%"
      duration: "2 min"

    - phase: 1
      name: "SCAN"
      executor: "@oalanicolas"
      input: [fontes_aprovadas, focus_areas]
      output: [candidatas_brutas]
      checkpoint: "candidatas >= 8"
      duration: "5-10 min"

    - phase: 2
      name: "FILTER"
      executor: "@oalanicolas"
      input: [candidatas_brutas]
      output: [candidatas_filtradas, classification_pareto]
      checkpoint: "generico_ratio <= 25%"
      duration: "3-5 min"

    - phase: 3
      name: "VALIDATE"
      executor: "@oalanicolas"
      input: [candidatas_filtradas]
      output: [candidatas_validadas, confidence_levels]
      checkpoint: "triangulation applied"
      duration: "3-5 min"

    - phase: 4
      name: "FORMALIZE"
      executor: "@oalanicolas"
      input: [candidatas_validadas]
      output: [heuristics_yaml, decision_cards, heuristic_files]
      checkpoint: "all have [SOURCE:], all SE/ENTÃO format"
      duration: "5-10 min"

    - phase: 5
      name: "DELIVER"
      executor: "@oalanicolas"
      input: [heuristics_yaml, decision_cards]
      output: [extraction_report, source_map, gap_report]
      checkpoint: "quality_check >= 6/7"
      duration: "2 min"

  tokens_consumed:
    - TKN-EXH-THR-001 (source traceability)
    - TKN-EXH-THR-002 (min candidatas)
    - TKN-EXH-THR-003 (max genérico ratio)
    - TKN-EXH-THR-004 (quality check score)
    - TKN-EXH-THR-005 (min ouro sources)
    - TKN-EXH-BEH-001 (triangulation)
    - TKN-EXH-BEH-002 (inference marking)
    - TKN-EXH-TAX-001 (heuristic types)
    - TKN-EXH-TAX-002 (pareto zones)
    - TKN-EXH-ACC-001 (accountability)
```

---

## Relationship with Session Heuristics

```yaml
extension_map:
  base: "an-extract-heuristics"
  specializations:
    - task_id: "an-extract-session-heuristics"
      focus: "Sessões de execução (commits, handoffs, bugs)"
      inherits:
        - "Pareto ao Cubo classification"
        - "SE/ENTÃO/NUNCA format"
        - "Quality check structure"
        - "3-Layer format (L1/L2/L3)"
        - "Veto pattern"
      adds:
        - "Phase 0: Session Eligibility (min duration, min decisions)"
        - "Worker de contexto automático (git-based)"
        - "Triangulação cross-session (promoção por recorrência)"
        - "Hook integration (post-session suggestion)"
        - "Memory routing (project memory update)"
      difference: |
        Base extrai de EXPERTS (fontes externas — livros, entrevistas, podcasts).
        Session extrai de EXECUÇÃO (o que aprendemos fazendo — commits, bugs, pivots).
        Base foca em "como o expert pensa".
        Session foca em "o que aprendemos rodando".
```

---

## Activation

Mission router do agente @oalanicolas:

```yaml
"*extract-heuristics":
  task: "tasks/an-extract-heuristics.md"
  data: null
```

**Invocação:** `*extract-heuristics`

---

*"Heurística sem [SOURCE:] é opinião. Opinião sem evidência é ruído. Curadoria > Volume."* 🧠
