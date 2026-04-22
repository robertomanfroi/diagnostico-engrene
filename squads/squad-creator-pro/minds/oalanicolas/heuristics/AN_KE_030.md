# AN_KE_030 - Anti-Fingerprint AI Detox

**Type:** Brand Safety Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Ghostwriting & Content Automation
**Source:** [SOURCE: Extraído de discussões sobre autoria fantasma, padronização de publicações e blindagem perceptual contra modelos sintéticos repetitivos.]
**sys_tension:** (authenticity_vs_efficiency, Resolve via human review gates and voice-injection formula that prioritizes authorial intent over production speed)

## Purpose

Garantir que os materiais construídos por agentes para clientes finais e consumo humano (livros, artigos, pitches, copy) nunca carreguem os "Marcadores Genéticos" de IA (existem frases, aberturas hiper-repetitivas e transições estruturais que depreciam imediatamente o valor percebido de conteúdos caros aos olhos de clientes seniores).

## Configuration

```yaml
AN_KE_030:
  name: "Anti-Fingerprint AI Detox"
  zone: "excelencia"
  trigger: "Gerando documentos públicos longos e copys assinados para clientes."

  rule: |
    SE você criar um conteúdo autoral em nome da Mentelendária
    ENTÃO DESTRUA qualquer marcador cognitivo clássico do Claude/GPT (ex: "Em resumo", emojis soltos sem motivo, aberturas formais "Certamente!").

  veto_condition:
    trigger: "Presença recorrente das frases sintéticas ou listas que seguem ritmos matemáticos previsíveis sem voz real."
    action: "VETO — Acione o revisor e quebre o padrão da comunicação com interrupções humanas (perguntas socráticas e imperfeições)."

  evidence:
    - "[EXACT WORDS]: A repetição mecânica destrói a percepção de alto valor. Remova 100% de assinaturas IA."

  tension_with: "AN_KE_025 (Determinism Over LLM) — Conflita porque determinismo preza saída previsível/matemática vs. necessidade aqui de injetar imperfeições humanas e variância autoral controlada."
```

## Decision Tree

```javascript
IF (generating_ghostwritten_article OR brand_material)
  IF (contains_trigger_phrases("Hoje vamos explorar...", "Em conclusão", "Em resumo"))
    THEN STRIP_AI_HOOKS
    THEN APPLY_ALAN_NICOLAS_VOICE_FORMULA
      IF (output_reads_synthetically_perfect)
        THEN INJECT_HUMAN_CONTRASTS (Break sentences, Socratic questioning, Analogies, Direct address)
  ELSE
    THEN FORWARD_TO_APPROVAL
```

## Failure Modes

### Percepção de Automação Barata
- **Trigger:** Ao processar o livro completo com a instrução "Resuma o capítulo sem quebrar o sentimento genuíno".
- **Manifestation:** O leitor, ao abrir o PDF "Premium", lê os clássicos "A inteligência artificial tem um papel fundamental neste mundo". Fica óbvio que foi um copy/paste automatizado sem esmero.
- **Detection:** Ferramentas de revisão notam repetição adverbial. O humano sente artificialidade.
- **Recovery:** Prompts limitadores com "Forbidden Words", passando um pente fino estilístico.
- **Prevention:** Incorporar ao Prompt a negativa absoluta dos metadados de máquina e remover a "vontade de agradar excessiva".

## Integration with Workflow

```yaml
checkpoint:
  id: "ai-detox-scanner"
  heuristic: AN_KE_030
  phase: "Content_Review"

  validation_questions:
    - "Eu publicaria isso sabendo que minha mãe leria e não desconfiaria da máquina?"
    - "A estética do livro preserva os solavancos naturais de uma mente pensante (TDAH e foco)?"

## Validation

**Paradox Identified:** The tension between automated content generation (efficiency) and authentic human voice (perception of value). AI agents can produce error-free, consistent prose at scale, but this very perfection signals synthetic origin to expert readers. Resolution requires systematic voice injection: breaking structural symmetry, introducing controlled imperfection, and embedding authorial quirks that prove human stewardship.

**Acceptance Criteria:**
- [ ] Output passes "mother test" — adult reader cannot distinguish synthesis from authorship
- [ ] Forbidden AI markers completely stripped (no "Em resumo", no mechanical transitions, no synthetic openings)
- [ ] Voice formula applied: Socratic questions, analogies, direct address, deliberate asymmetries
- [ ] Human review checkpoint mandatory for materials >2K words or client-facing copy
- [ ] Revision feedback loop captures idiosyncratic voice patterns for future generations
```
