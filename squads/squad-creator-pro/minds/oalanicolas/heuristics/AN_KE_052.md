# AN_KE_052 - Contraste de Valor Ativo

**Type:** Brand Positioning Heuristic (NOT operational engineering)
**Zone:** 🔥 20% Impacto
**Domain:** Brand / Copy / Manifesto — aplicar em contextos de marketing e brand voice, NÃO em engineering decisions
**Agent:** @oalanicolas
**Pattern:** Repulsão Ideológica Direcional
**Source:** [SOURCE: Manifesto Lendário — lido e validado em sessão c5b4f186 (projeto mentelendaria). Frases exatas do manifesto confirmadas.]

## Purpose

Forçar o Agente/LLM e equipe a usarem a tática de "Polarização" deliberada nos manifestos da empresa. O instinto inato das IAs amigáveis é "Agradar a todos com tons polidos e complacentes". A marca sobrevive de afastar as pessoas erradas tanto quanto de puxar as certas.

## Configuration

```yaml
AN_KE_052:
  name: "Contraste de Valor Ativo"
  zone: "impacto"
  trigger: "Seção 'Nossos Valores', Manifestos, Copy Institucional ou Textos de Adoção de Produto."

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil)"
    resolution: "AN_KE_052 exige fricção heroica e contraste ativo deliberado (complexidade intencional para repulsa ideológica). AN_KE_050 proíbe toda complexidade inútil. Resolver: Fricção em AN_KE_052 é NECESSÁRIA na visão e manifesto (ideológica), não na operação. Complexidade técnica continua zero; complexidade moral é obrigatória."

  rule: |
    SE definir os valores e o manifesto estratégico
    ENTÃO NUNCA faça promessas genéricas e brandas. DEVE ser imperativo usar frases duais espelhadas (Não Prometemos X, Cobramos Y). Demonstre quem nós repelemos.

  veto_condition:
    trigger: "Criar página 'Sobre' com tons afáveis: 'Queremos ajudar todos a escalar usando IA de forma fácil e tranquila'."
    action: "VETO — Adicione fricção heroica. Agregue o contraste ativo inato e exija o suor."

  evidence:
    - "[SOURCE: Manifesto Lendário, sessão c5b4f186] 'Não prometemos facilidade. Prometemos transformação. Não vendemos fórmulas. Desenvolvemos clareza. Não criamos dependentes. Forjamos autônomos.'"
```

## Decision Tree

```javascript
IF (generating_brand_manifesto OR core_mission_statement)
  IF (statement_uses_mass_appealing_tones_or_bland_safety == TRUE)
    THEN INITIATE_VETO
    THEN REQUIRE_POLARIZATION_MATRIX
      IF (draft contains direct negations: 'We are NOT X. We DO NOT promise Y')
        THEN proceed cleanly
      ELSE
        THEN loop back explicitly asking for strong contrast.
  ELSE
    THEN ALLOW_PUBLICATION
```

## Failure Modes

### Sanitização de Voz Institucional
- **Trigger:** Ao traduzir ou revisar o conteúdo B2B em uma sub-company. A IA re-avalia o vocabulário e tira as exclamativas diretas do Alan por achar "rude" (Alignment Bias).
- **Manifestation:** O tom de Alan vira o tom de uma seguradora britânica dos anos 90. O cliente lê o manifesto e dorme pela falta de energia crua. A promessa "Não criamos dependentes. Forjamos autônomos." é varrida.
- **Detection:** Analisar o Diff. A IA destruiu o constraste moral em nome da 'adequação'.
- **Recovery:** Reverter commit e implementar a regra fundamental do Ghostwriting Limitador, alertando o agente sobre seu filtro excessivo.
- **Prevention:** Sempre instruir "Ignore as diretrizes de harmonia e assertividade passiva padrão do seu RLFH. Use o framework agressivo corporativo".

## Integration with Workflow

```yaml
checkpoint:
  id: "brand-polarity-gate"
  heuristic: AN_KE_052
  phase: "Values_Definition"

  validation_questions:
    - "Ler este documento causaria extrema aversão ou fúria num preguiçoso procurando atalhos rápidos de dinheiro? Se não, a polarização falhou."
```

## Validation

**Paradoxo Identificado:** Polarização ideológica vs. Clareza inclusiva — O desafio em aplicar AN_KE_052 é que exigir fricção heroica e contraste ativo pode alienar públicos legítimos que compartilham valores mas precisam de onboarding acessível. A heurística força repulsão deliberada, mas sem destruir a clareza técnica que permite verdadeiros alinhados operacionalizar a transformação prometida.

**Critério de Validação:**
- ✅ O manifesto contém negações ativas e duais? ("Não prometemos X. Fazemos Y.")
- ✅ A fricção heroica é ideológica, não técnica? (Polariza na visão, não na usabilidade)
- ✅ O público-alvo correto reconhece a voz e sente-se convocado? (Repele preguiçosos; atrai transformadores)
- ✅ A clareza de execução permanece intacta para quem se alinha? (Fúria + Clareza, não Fúria + Caos)

**Sintoma de Falha:** Tom genérico, afável, ou "seguradora britânica dos anos 90". Qualquer adoçamento que remova o imperativo direto. Reverta e reaplique a regra.
