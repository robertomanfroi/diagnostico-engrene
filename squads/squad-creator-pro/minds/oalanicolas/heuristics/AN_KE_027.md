# AN_KE_027 - Zero Emojis & Design Consistente

**Type:** Design Standard Heuristic
**Zone:** 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Rigor Visual, Shadcn & Tailwind
**Source:** [SOURCE: Extraído de guidelines e feedbacks onde o uso superficial de emojis infantiliza a UI profissional premium da marca.]

**sys_tension:** (rigor_visual_absoluto, comunicação_visual_eficaz) → Resolver: Emojis permitidos apenas em docs internas, conversas, e metadata; proibidos em interfaces finais ao cliente

## Purpose

Estabelecer a barreira de maturidade visual do software (dashboards, relatórios gerenciais e interfaces de linha de comando visuais para clientes premium). A proliferação de emojis desvaloriza a estética elegante e reduz o senso de robustez e sofisticação (premium design).

## Configuration

```yaml
AN_KE_027:
  name: "Zero Emojis & Design Consistente"
  zone: "impacto"
  trigger: "Criando interfaces gráficas, painéis de admin, Readme.md de cliente ou relatórios executivos finais."

  rule: |
    SE for renderizar dados ao usuário
    ENTÃO substitua 100% dos 🚀🔥✅ por ícones baseados em SVG/Lucide com Tailwind estrito.
    Não dependa de Emojis do OS pois sua variação quebra a tipografia corporativa.

  veto_condition:
    trigger: "Detecção de Unicode Emojis fora de commits ou conversas internas."
    action: "VETO — Remover emoji, substituir por Lucide Icon nativo ou texto em Tailwind."

  evidence:
    - "[EXACT WORDS]: NUNCA use emojis. Use SVGs/Lucide e Tailwind/Shadcn rigorosos para interfaces finais."

  tension_with: "AN_KE_047 (AI-Predictable Design Systems) — Sistemas de design podem incluir emojis como tokens visuais previsíveis, criando conflito com a proibição absoluta aqui"
```

## Decision Tree

```javascript
IF (creating_ui_for_client OR reporting_managerial_status)
  IF (contains_emoji_character)
    THEN STRIP_EMOJIS
    THEN MAP_TO_LUCIDE_ICON (e.g. ⚠️ -> AlertCircle, ✅ -> CheckCircle2)
      IF (Lucide_not_available)
        THEN use empty string OR pure typographic contrast (bold/accent color)
  ELSE
    THEN ALLOW_RENDERING
```

## Failure Modes

### Infantilização do Brand
- **Trigger:** Renderização padrão do LLM ao gerar listas HTML ou Markdown.
- **Manifestation:** Dashboard analítico de $5k apresentando relatórios financeiros cheios de "💸💰📈".
- **Detection:** Inspeção visual denota uma estética juvenil num SaaS premium.
- **Recovery:** Regexec `[🚀🔥💸...]` e buscar substitutos modulares.
- **Prevention:** Passar guidelines rigorosas no prompt limitador ou proibir Unicode block.

## Integration with Workflow

```yaml
checkpoint:
  id: "zero-emoji-gate"
  heuristic: AN_KE_027
  phase: "UI_Development"

  validation_questions:
    - "Existe algum emoji preenchendo o papel de um ícone vetorial legítimo?"
    - "O espaçamento de tipografia respeita as regras nativas de Shadcn?"
```

## Validation

**Paradoxo Identificado:** A heurística proíbe emojis em UIs profissionais, mas usa emojis em sua própria documentação (🔥, 💸, 📈, etc.) para comunicação interna.

**Resolução:** Emojis são permitidos em:
- Documentação interna (heurísticas, checklists, conversas)
- Metadata e zona de impacto
- Conversas entre agentes
- Markdown de conhecimento compartilhado (KNOWLEDGE BOUNDARY)

**Proibição:** Emojis em renderização final para cliente (dashboards, relatórios executivos, interfaces públicas).

**Status:** ✓ Heurística válida e aplicável após distinção de contexto.
