# AN_KE_047 - AI-Predictable Design Systems

**Type:** Modern Architecture Standard
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Machine-Readable Tokenization
**Source:** [SOURCE: Criação do Academia Lendária Framework, focando a utilidade do Shadcn não só para humanos, mas também para consumo direto das prompts da LLM.]

## Purpose

Tornar o repositório perfeitamente auditável por IA. Se existirem 90 camadas de CSS modules anônimos separados cruzando SASS global solto, a IA enlouquece toda vez que precisar renderizar uma Landing Page. Ferramentas preditivas (Tailwind + CVA + Shadcn estritos) funcionam porque a API da camada de Design vira um Lego Lógico que modelos de linguagem conseguem decodificar cegamente sem precisar bater olho num figma.

## Configuration

```yaml
AN_KE_047:
  name: "AI-Predictable Design Systems"
  zone: "excelencia"
  trigger: "Criando ou editando as guias de interface, Design Systems e Repositórios Visuais num mundo LLM-first."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Complexidade de Parsing Local"
    resolution: "CVA Variants as Bridge — Permite expressão criativa humana através de composições semânticas predizíveis para IA. O Designer define as variantes (art), a IA as combina (logic). Sistemas previsíveis para IA requerem linearidade; paralelização introduz não-determinismo."

  rule: |
    SE for adotar um framework de CSS/Design System
    ENTÃO NUNCA permita configurações caóticas puramente visuais (como "SASS classes com 99 variaveis de rem magicas"). Trabalhe em lógicas nominais rígidas (CVA) onde a sintaxe por si só revele para o Claude qual a variação a se escalar e usar.

  veto_condition:
    trigger: "Criar variações customizadas sem atrelar Variância Explícita de Componentes (ex: `<Button className='bg-red text-2xl...' />`)."
    action: "VETO — Encapsule dentro da Variante do Design System: `<Button variant='destructive' size='lg' />`."

  evidence:
    - "[EXACT WORDS]: Tailwind + shadcn/ui + CVA é literalmente a combinação perfeita pra transformar esse Brand Guide... E o fato de IAs também vão usar? Isso muda o jogo — precisa ser extremamente previsível."
```

## Decision Tree

```javascript
IF (styling_new_interface OR modifying_ui_elements)
  IF (style_uses_loose_magic_variables_or_arbitrary_tailwind == TRUE)
    THEN BLOCK_FRONTEND_COMMIT
    THEN REQUIRE_CVA_ENCAPSULATION
      IF (component properly defines 'variants' mapping to the Brand Design System standard)
        THEN proceed scaling with AI automation smoothly
  ELSE
    // Component is correctly utilizing the highly strict 'Tailwind->CVA->Shadcn' pipeline
    THEN ALLOW_RENDER
```

## Failure Modes

### Hallucination UI Break
- **Trigger:** IA tenta criar versão de tela preta e falha brutalmente, colapsando classes text-black no meio.
- **Manifestation:** Em vez de usar a variação inteligente e legível que o CVA possibilita (`variant='dark_mode_inverted'`), a LLM tentou adivinhar com `className="dark:bg-black dark:text-gray-100 ..."`. Em uma lista extensa de cards customizados quebrando padronizações.
- **Detection:** Análise de commits front-end mostrando desprendimento crônico do padrão primário (O botão padrão deixou de ser usado).
- **Recovery:** Refatorar todos os componentes livres e criar Variantes Globais na CVA core baseadas nos arquivos mestre.
- **Prevention:** Veto-Gates de Lint impedindo componentes customizados demais que rejeitassem a biblioteca central.

## Integration with Workflow

```yaml
checkpoint:
  id: "ai-readable-cva-gate"
  heuristic: AN_KE_047
  phase: "Frontend_Design_Architect"

  validation_questions:
    - "A LLM v3/v4 conseguirá prever com confiança absoluta o resultado visual que o Tailwind+CVA irá compilar para essa marca ao bater a variante exata 'accent'?"
```

## Validation

- **Paradoxo Identificado:** Rigidez estrutural (CVA nominais) vs. Liberdade criativa do designer humano. Resolução através de variantes semânticas que são rígidas para IA mas flexíveis para composição humana.
- **Checkpoint:** Verificar se 100% dos componentes novos passam pela gate `ai-readable-cva-gate` antes de merge.
- **Métrica:** Zero commits front-end com classes Tailwind arbitrárias fora do CVA core.
- **Escalabilidade:** CVA deve ser auditável por `grep` — se a variante não está no arquivo core, ela não deveria existir.
