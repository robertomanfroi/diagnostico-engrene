---
task-id: evd-extract-dimensions
name: "Voice DNA: Extract All 7 Dimensions"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Semantic extraction across 7 voice dimensions requires deep language interpretation -- not deterministic"
estimated-time: 45 min
complexity: medium

inputs:
  required:
    - validated_sources: "Lista validada de 5+ fontes (output from evd-collect-sources)"
    - mind_name: "Nome do expert/mind a clonar"

outputs:
  primary:
    - voice_dimensions: "YAML com vocabulary, storytelling, writing_style, tone, anti_patterns, immune_system, voice_contradictions"

elicit: true
parent_task: extract-voice-dna.md
related_tasks:
  - evd-collect-sources.md
  - evd-assemble-voice-dna.md
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: evd-extract-dimensions
  task_name: 'Voice DNA: Extract All 7 Dimensions'
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 45m
  domain: Operational
  input:
  - '{''validated_sources'': ''Lista validada de 5+ fontes (output from evd-collect-sources)''}'
  - '{''mind_name'': ''Nome do expert/mind a clonar''}'
  output:
  - '{''voice_dimensions'': ''YAML com vocabulary, storytelling, writing_style, tone, anti_patterns, immune_system, voice_contradictions''}'
  action_items:
  - 'Step 1: Extract Vocabulary (power words, signature phrases, metaphors, rules)'
  - 'Step 2: Extract Storytelling Patterns (recurring stories, anecdotes, examples, structure)'
  - 'Step 3: Extract Writing Style (structure, rhetorical devices, formatting, sentence patterns)'
  - 'Step 4: Extract Tone Profile (voice dimensions 1-10, contextual tone, identity statement)'
  - 'Step 5: Extract Anti-Patterns (never-say, never-do, rejected styles)'
  - 'Step 6: Extract Immune System (automatic rejections, emotional boundaries, fierce defenses)'
  - 'Step 7: Extract Contradictions (paradoxes, inconsistencies, preservation instructions)'
  acceptance_criteria:
  - 10+ power words with [SOURCE:] citations [threshold: >= 10]
  - 8+ signature phrases with example_usage [threshold: >= 8]
  - 3+ metaphors documented [threshold: >= 3]
  - Vocabulary rules defined (always_use, never_use, transforms) [threshold: >= 3]
  - 3+ recurring stories with triggers and lessons [threshold: >= 3]
  - Personal anecdotes with emotional tone mapping [threshold: >= 1]
  - Favorite examples catalogued with frequency [threshold: >= 1]
  - Story structure fully mapped (opening, build_up, payoff, callback) [threshold: >= 4]
  - Text structure fully mapped (paragraph, sentence, list, headers) [threshold: >= 4]
  - All 6 rhetorical device dimensions analyzed [threshold: >= 6]
  - Formatting habits documented [threshold: >= 1]
  - 3-5 sentence patterns with [SOURCE:] citations and when_to_use [threshold: >= 3]
  - All 7 voice dimensions calibrated (not default 5) [threshold: >= 7]
  - Each dimension justified with observed evidence [threshold: >= 7]
  - All 5 contextual tones defined [threshold: >= 5]
  - Identity statement crafted (Trinity Phrase) [threshold: >= 1]
  - 5+ anti-patterns with example_wrong + example_correct [threshold: >= 5]
  - Behavioral avoidances documented with workarounds [threshold: >= 1]
  - Rejected styles identified [threshold: >= 1]
  - 2+ automatic rejections with triggers and responses [threshold: >= 2]
  - Emotional boundaries mapped with intensity ratings [threshold: >= 1]
  - Fierce defenses identified with cost tolerance [threshold: >= 1]
  - 1+ paradox/contradiction documented [threshold: >= 1]
  - Each paradox has clone_instruction (do NOT resolve) [threshold: >= 1]
  - Triggers for switching between contradictory modes identified [threshold: >= 1]
  - ZERO content invented -- all extracted from sources [threshold: == 0]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Voice DNA -- Extract All 7 Dimensions

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `evd-extract-dimensions` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `agent` |

## Metadata

- **Parent:** `extract-voice-dna.md`
- **Phase:** 2 of 3 (collect --> **extract** --> assemble)
- **Model:** Opus (semantic pattern extraction across 7 dimensions requires deep language interpretation)
- **Replaces:** 7 former atomic tasks (evd-extract-vocabulary, evd-extract-storytelling, evd-extract-writing-style, evd-extract-tone, evd-extract-anti-patterns, evd-extract-immune-system, evd-extract-contradictions)

## Purpose

Extract all 7 voice dimensions from source material in a single pass. Each step produces a YAML block with source citations. All 7 blocks are combined into the `voice_dimensions` output for assembly.

> These are steps in a linear pipeline, not independent atomic tasks. One executor, one context, one pass.

## Prerequisites

- `evd-collect-sources` completed with 5+ validated sources (tier ouro/bronze)
- Source materials accessible for citation

## Inputs

| Input | Type | Required | Description |
|-------|------|----------|-------------|
| `validated_sources` | list | Yes | Output from evd-collect-sources (5+ sources with tier classification) |
| `mind_name` | string | Yes | Nome do expert/mind a clonar |

## Workflow / Steps

---

### Step 1: Extract Vocabulary

Palavras que o expert usa REPETIDAMENTE com peso emocional, frases que o IDENTIFICAM, metaforas favoritas e regras de vocabulario.

#### 1.1 Power Words (10-15)

```yaml
power_words:
  - word: ""
    source: "[SOURCE: documento, pagina/secao]"  # OBRIGATORIO
    context: "quando usa"
    emotional_weight: "alto|medio"
```

**REGRA:** Cada power word DEVE ter `source:` com citacao exata.

#### 1.2 Signature Phrases (8-12)

```yaml
signature_phrases:
  - phrase: ""
    source: "[SOURCE: documento, pagina/secao]"  # OBRIGATORIO
    meaning: ""
    use_when: ""
    example_usage: ""  # Como usar em copy NOVO (nao so citar)
```

**REGRA:** Cada frase DEVE ter:
- `source:` com citacao exata
- `example_usage:` mostrando aplicacao pratica

#### 1.3 Favorite Metaphors (3-5)

```yaml
metaphors:
  - concept: "o que explica"
    metaphor: "como explica"
    example: ""
```

#### 1.4 Vocabulary Rules

```yaml
vocabulary_rules:
  always_use: []    # termos que SEMPRE usa
  never_use: []     # termos que EVITA
  transforms:       # como "traduz" jargao
    - from: "jargao comum"
      to: "como ele diz"
```

#### Step 1 Output

```yaml
vocabulary:
  power_words: []
  signature_phrases: []
  metaphors: []
  rules:
    always_use: []
    never_use: []
    transforms: []
```

---

### Step 2: Extract Storytelling Patterns

Historias que o expert conta REPETIDAMENTE, anedotas pessoais, exemplos favoritos e a estrutura narrativa.

#### 2.1 Recurring Stories

```yaml
recurring_stories:
  - title: "Nome/descricao curta"
    summary: "O que acontece"
    lesson: "O ponto que ilustra"
    trigger: "Quando conta essa historia"
    source: "Onde aparece"
```

#### 2.2 Personal Anecdotes

```yaml
personal_anecdotes:
  - event: ""
    lesson_extracted: ""
    emotional_tone: ""
    use_for: "tipo de argumento que suporta"
```

#### 2.3 Favorite Examples

```yaml
favorite_examples:
  - example: ""
    domain: ""
    point_it_makes: ""
    frequency: "sempre|frequente|ocasional"
```

#### 2.4 Story Structure

```yaml
story_structure:
  opening: "como comeca historias"
  build_up: "como desenvolve tensao"
  payoff: "como entrega o ponto"
  callback: "se/como referencia de volta"
```

#### Step 2 Output

```yaml
storytelling:
  recurring_stories: []
  personal_anecdotes: []
  favorite_examples: []
  story_structure:
    opening: ""
    build_up: ""
    payoff: ""
    callback: ""
```

---

### Step 3: Extract Writing Style

Estrutura textual, dispositivos retoricos, habitos de formatacao e padroes de sentenca.

#### 3.1 Text Structure

```yaml
writing_structure:
  paragraph_length: "curto|medio|longo"
  sentence_length: "curta|media|longa"
  list_usage: "frequente|moderado|raro"
  headers_style: ""
  opening_pattern: "como abre textos/secoes"
  closing_pattern: "como fecha textos/secoes"
```

#### 3.2 Rhetorical Devices

```yaml
rhetorical_devices:
  questions: "usa perguntas retoricas? como?"
  repetition: "usa repeticao? padrao?"
  contrast: "usa contraste? padrao?"
  direct_address: "fala direto com leitor? como?"
  humor: "usa humor? tipo?"
  provocation: "provoca? como?"
```

#### 3.3 Formatting Habits

```yaml
formatting_habits:
  emphasis: "negrito|italico|CAPS|aspas"
  parentheses: "frequente|raro"
  dashes: "frequente|raro"
  ellipsis: "frequente|raro"
  special_chars: []  # ex: "->", "*", etc
```

#### 3.4 Sentence Patterns (3-5)

```yaml
sentence_patterns:
  - pattern: "Nome do padrao"
    description: "O que caracteriza"
    example: "Exemplo real do expert"
    source: "[SOURCE: documento, pagina]"
    when_to_use: "Quando aplicar esse padrao"

# Exemplos de padroes comuns:
# - Fragmentos curtos para enfase: "A starving crowd. That's what you need."
# - Anafora (repeticao): "Hard work. Daily work. Consistent work."
# - Escolhas binarias: "You can be a whiner or you can be a winner."
# - Imperativos diretos: "Listen up. Read this carefully."
```

#### Step 3 Output

```yaml
writing_style:
  structure:
    paragraph_length: ""
    sentence_length: ""
    list_usage: ""
    headers_style: ""
    opening_pattern: ""
    closing_pattern: ""
  sentence_patterns: []
  rhetorical_devices:
    questions: ""
    repetition: ""
    contrast: ""
    direct_address: ""
    humor: ""
    provocation: ""
  formatting:
    emphasis: ""
    parentheses: ""
    dashes: ""
    ellipsis: ""
    special_chars: []
```

---

### Step 4: Extract Tone Profile

Dimensoes de voz calibradas em escala 1-10, tom contextual e a identity statement.

#### 4.1 Voice Dimensions (1-10)

```yaml
voice_dimensions:
  warmth_distance: 5      # 1=caloroso, 10=distante
  direct_indirect: 5      # 1=direto, 10=indireto
  formal_casual: 5        # 1=formal, 10=casual
  complex_simple: 5       # 1=complexo, 10=simples
  emotional_rational: 5   # 1=emocional, 10=racional
  humble_confident: 5     # 1=humilde, 10=confiante
  serious_playful: 5      # 1=serio, 10=brincalhao
```

**REGRA:** NAO deixar valores default 5. Cada dimensao deve ser calibrada com evidencia observada nas fontes.

#### 4.2 Contextual Tone

```yaml
contextual_tone:
  teaching: ""        # quando ensina
  persuading: ""      # quando convence
  storytelling: ""    # quando conta historia
  criticizing: ""     # quando critica
  celebrating: ""     # quando elogia
```

#### 4.3 Identity Statement

The Trinity Phrase that captures the expert's communication essence:

> "[Nome] escreve/fala como ________________"

This single sentence must be distinctive enough that someone familiar with the expert would immediately recognize them from it.

#### Step 4 Output

```yaml
tone:
  dimensions:
    warmth_distance: 0
    direct_indirect: 0
    formal_casual: 0
    complex_simple: 0
    emotional_rational: 0
    humble_confident: 0
    serious_playful: 0
  by_context:
    teaching: ""
    persuading: ""
    storytelling: ""
    criticizing: ""
    celebrating: ""
  identity_statement: ""
```

---

### Step 5: Extract Anti-Patterns

O que o expert NUNCA faz ou diz em comunicacao. Anti-patterns definem o espaco negativo da voz.

#### 5.1 Never-Say Terms (5+)

```yaml
communication_anti_patterns:
  never_say:
    - term: ""
      source: "[SOURCE: inferido de documento, pagina]"  # De onde inferiu
      reason: "Por que evita"
      substitute: "O que usa no lugar"
      example_wrong: "Frase que violaria a voz"
      example_correct: "Frase corrigida na voz do expert"
```

**REGRA:** Cada anti-pattern DEVE ter:
- `example_wrong:` mostrando o que NAO fazer
- `example_correct:` mostrando a correcao na voz do expert

#### 5.2 Behavioral Avoidances

```yaml
never_do_communication:
  - behavior: ""
    context: ""
    reason: ""
    workaround: "como contorna"
```

#### 5.3 Rejected Styles

```yaml
rejected_styles:
  - style: ""
    reason: ""
    observed_discomfort: "como reage quando forcado"
```

#### Step 5 Output

```yaml
anti_patterns:
  never_say: []
  never_do: []
  rejected_styles: []
```

---

### Step 6: Extract Immune System

O que o expert rejeita ANTES mesmo de pensar -- respostas reflexivas automaticas a gatilhos. Limites hardcoded da voz.

#### 6.1 Automatic Rejections

```yaml
automatic_rejections:
  - trigger: ""
    response_speed: "imediato|rapido|apos reflexao"
    typical_response: ""
    tone_shift: "como o tom muda"
    exceptions: "quando aceita"
```

#### 6.2 Emotional Boundaries

```yaml
emotional_boundaries:
  - boundary: ""
    auto_defense: "como reage"
    intensity: "1-10"
    recovery_time: "quanto tempo para voltar ao normal"
```

#### 6.3 Fierce Defenses

```yaml
fierce_defenses:
  - value: ""
    how_hard: "ate onde vai"
    cost_acceptable: "disposto a perder relacionamento?"
    observable_signs: "como perceber que ativou"
```

#### Step 6 Output

```yaml
immune_system:
  automatic_rejections: []
  emotional_boundaries: []
  fierce_defenses: []
```

---

### Step 7: Extract Contradictions

Contradicoes e paradoxos autenticos. Contradicoes fazem humanos REAIS. Resolver paradoxos faz clones FALSOS.

> Contradicoes sao features, nao bugs. Se o clone for "consistente demais", esta errado.

#### 7.1 Communication Paradoxes

```yaml
voice_contradictions:
  - paradox: ""
    how_appears: "Como isso aparece na fala/escrita"
    trigger_for_switch: "O que faz mudar de um para outro"
    audience_dependent: "Muda com diferentes audiencias?"
    clone_instruction: "NAO RESOLVER - preservar o paradox"
```

#### 7.2 Authentic Inconsistencies

```yaml
authentic_inconsistencies:
  - inconsistency: ""
    context_A: "quando faz X"
    context_B: "quando faz Y (oposto)"
    why_both_are_authentic: ""
```

#### 7.3 Clone Preservation Instructions

```yaml
paradox_handling:
  preserve_these:
    - "Lista de paradoxos que NAO devem ser resolvidos"

  guidance: |
    Contradicoes sao features, nao bugs.
    Se o clone for "consistente demais", esta errado.
```

#### Step 7 Output

```yaml
voice_contradictions:
  paradoxes: []
  authentic_inconsistencies: []
  preservation_note: |
    Contradicoes sao features, nao bugs.
    Clone "consistente demais" = clone falso.
```

---

## Combined Output

All 7 step outputs combined into a single `voice_dimensions` block:

```yaml
voice_dimensions:
  vocabulary:
    power_words: []
    signature_phrases: []
    metaphors: []
    rules: {}

  storytelling:
    recurring_stories: []
    personal_anecdotes: []
    favorite_examples: []
    story_structure: {}

  writing_style:
    structure: {}
    sentence_patterns: []
    rhetorical_devices: {}
    formatting: {}

  tone:
    dimensions: {}
    by_context: {}
    identity_statement: ""

  anti_patterns:
    never_say: []
    never_do: []
    rejected_styles: []

  immune_system:
    automatic_rejections: []
    emotional_boundaries: []
    fierce_defenses: []

  voice_contradictions:
    paradoxes: []
    authentic_inconsistencies: []
    preservation_note: ""
```

## Acceptance Criteria

### Vocabulary (Step 1)
- [ ] 10+ power words extracted with [SOURCE:] citations [threshold: >= 10]
- [ ] 8+ signature phrases with `example_usage:` (new copy, not just citation) [threshold: >= 8]
- [ ] 3+ metaphors documented [threshold: >= 3]
- [ ] Vocabulary rules defined (always_use, never_use, transforms) [threshold: >= 3]
- [ ] ZERO content invented -- all extracted from sources [threshold: == 0]

### Storytelling (Step 2)
- [ ] 3+ recurring stories documented with triggers and lessons [threshold: >= 3]
- [ ] Personal anecdotes extracted with emotional tone mapping [threshold: >= 1]
- [ ] Favorite external examples catalogued with frequency [threshold: >= 1]
- [ ] Story structure pattern fully mapped (opening, build_up, payoff, callback) [threshold: >= 4]
- [ ] All stories traceable to source materials [threshold: score >= 0.8]

### Writing Style (Step 3)
- [ ] Text structure fully mapped (paragraph, sentence, list, headers, patterns) [threshold: >= 5]
- [ ] All 6 rhetorical device dimensions analyzed [threshold: >= 6]
- [ ] Formatting habits documented [threshold: >= 1]
- [ ] 3-5 sentence patterns extracted with real examples and [SOURCE:] citations [threshold: >= 3]
- [ ] Each sentence pattern has `when_to_use` guidance [threshold: >= 3]

### Tone Profile (Step 4)
- [ ] All 7 voice dimensions calibrated (not left at default 5) [threshold: >= 7]
- [ ] Each dimension justified with observed evidence from sources [threshold: >= 7]
- [ ] All 5 contextual tones defined [threshold: >= 5]
- [ ] Identity statement crafted (Trinity Phrase) [threshold: >= 1]
- [ ] Identity statement is distinctive and recognizable [threshold: score >= 0.8]

### Anti-Patterns (Step 5)
- [ ] 5+ anti-patterns of communication documented [threshold: >= 5]
- [ ] ALL anti-patterns have `example_wrong:` + `example_correct:` [threshold: score >= 0.8]
- [ ] All anti-patterns have `source:` with inference citation [threshold: score >= 0.8]
- [ ] `example_correct` sounds like the expert would actually say it [threshold: score >= 0.8]
- [ ] Behavioral avoidances documented with workarounds [threshold: >= 1]
- [ ] Rejected styles identified with discomfort observations [threshold: >= 1]

### Immune System (Step 6)
- [ ] 2+ automatic rejections documented with triggers and responses [threshold: >= 2]
- [ ] Tone shift documented for each rejection (how voice changes under trigger) [threshold: >= 2]
- [ ] Emotional boundaries mapped with intensity ratings [threshold: >= 1]
- [ ] Fierce defenses identified with cost tolerance [threshold: >= 1]
- [ ] All entries traceable to observed behavior in sources [threshold: score >= 0.8]

### Contradictions (Step 7)
- [ ] 1+ paradox/contradiction documented [threshold: >= 1]
- [ ] Each paradox has `clone_instruction` explicitly saying NOT to resolve it [threshold: >= 1]
- [ ] Trigger for switching between contradictory modes identified [threshold: >= 1]
- [ ] Audience dependency analyzed [threshold: >= 1]
- [ ] Preservation note included for clone guidance [threshold: >= 1]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EVD-003 | All entries must have SOURCE citations | Validate every vocabulary/pattern entry has non-empty source field with [SOURCE: doc, page] format | VETO - BLOCK. Remove uncited entries or find supporting source references. |

## Related Documents

- `extract-voice-dna.md` (parent orchestrator)
- `evd-collect-sources.md` (prerequisite -- provides validated sources)
- `evd-assemble-voice-dna.md` (next step -- assembles and quality-checks)
