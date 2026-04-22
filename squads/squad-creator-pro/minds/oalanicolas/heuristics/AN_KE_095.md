# AN_KE_095 - Prompt Over Code for Control
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão Hackathon-Hub 066cd683 — reverter código e deixar controle no prompt]

## Purpose

Às vezes a solução não é mais código — é melhor prompt/config. Se algo pode ser controlado via prompt (formato de output, comportamento de avaliação), é mais flexível e barato que hardcodar no código.

## Configuration

```yaml
AN_KE_095:
  name: "Prompt Over Code for Control"
  zone: "excelencia"
  trigger: "Implementando lógica que depende de formato/comportamento ajustável."

  rule: |
    SE controle pode ser no prompt/config ao invés de no código
    ENTÃO prompt > code. Mais flexível, mais barato de iterar.
    "vamos reverter tudo entao e deixar o controle no prompt"

  evidence:
    - "[SOURCE: sessão 066cd683, Hackathon-Hub] 'vamos reverter tudo entao e deixar o controle no prompt'"

  sys_tension:
    tension_with: "AN_KE_025 (Determinism Over LLM) vs Prompt Flexibility"
    resolution: |
      Prompt é mais barato que código, MAS prompt drift sem versionamento é mais caro que código.
      Balancear: use prompt para comportamento ajustável, MAS versione prompts (git + prompt_registry.yaml).
      Sem versionamento → máximo 30 dias antes de risco de drift incontrolável.
```

## Decision Tree

```javascript
IF (implementing_behavior_control)
  CHECK: can this be controlled via prompt/config instead of code?
    IF (output format) → prompt instruction > code parser
    IF (evaluation criteria) → prompt rubric > hardcoded scoring
    IF (behavior toggle) → config flag > if/else in code
    IF (complex logic with edge cases) → code is appropriate
  BENEFIT: prompt changes = instant deploy, no build needed
  RISK: prompt drift — version control prompts like code
```

## Failure Modes

### O Parser que Deveria Ser Prompt
- **Trigger:** 200 lines of code to parse LLM output format → could be fixed with 1 prompt line.
- **Manifestation:** "vamos reverter tudo e deixar o controle no prompt."
- **Detection:** Code that parses/formats LLM output extensively.
- **Prevention:** Ask: "can a prompt instruction replace this code?" If yes → prompt > code.

## Validation

✅ **Heurística validada:** Prompt como instrumento de controle é mais eficiente que hardcoding, DESDE QUE prompts sejam versionados como código.
⚠️ **Tensão sistêmica:** Prompt drift (mudanças não documentadas) pode cancelar todo benefício de flexibilidade. Exigir: `prompt_registry.yaml` + git commits para todas as mudanças de prompt.
📋 **Critério de aceitação:** Qualquer mudança de prompt deve ser: (1) documentada em git, (2) rastreável em `prompt-changelog.md`, (3) validada contra casos de teste antes de deploy.
