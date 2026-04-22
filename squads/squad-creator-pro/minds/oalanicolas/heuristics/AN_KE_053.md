# AN_KE_053 - Regra da Exclusividade Visual

**Type:** Design Governance Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Refatoramento Escalável Front-End
**Source:** [SOURCE: Extraídos do Academia Lendar[ia] Design System Framework para frear Customizações Inúteis no Shadcn.]

## Purpose

Assegurar a manutenibilidade a longo prazo usando ferramentas como Shadcn UI e Tailwind. Desenvolvedores medíocres (e as LLMs em threads soltas) destroem a componentização sobrescrevendo tudo que tocam com hex-colors locais invés de confiar nas regras nativas do pacote global. Apenas detalhes cruciais que gritam "Marca" merecem sobrescrita.

## Configuration

```yaml
AN_KE_053:
  name: "Regra da Exclusividade Visual"
  zone: "excelencia"
  trigger: "Quando forçados estilizações manuais em Tailwind ou instanciando componentes Shadcn UI prontos no React."

  sys_tension:
    tension_with: "AN_KE_047 (AI-Predictable Design Systems) — Customizações ad-hoc na UI destroem previsibilidade de padrões que AI depende; vs AN_KE_053 demanda sobrescrita visual mínima mas intencional para marca"
    resolution: "Permitir overrides APENAS nas chaves sagradas da marca (dourado, monocromático, cantos). Tudo mais: usar defaults."

  rule: |
    SE o componente raiz (base) do shadcn e o tema default resolverem bem
    ENTÃO DEIXE-O RESPIRAR.
    SÓ aplique overrides visuais fortes nas exatas chaves visuais sagradas da Academia (Ex: O detalhe Dourado como Acento, O esquema Monocromático Absoluto, Formas Rígidas de cantos).

  veto_condition:
    trigger: "Modificar dezenas de `padding=6` do core Button sem motivo, e quebrar a simetria orgânica e acessibilidade nativa construída pelos criadores do Shadcn/Radix."
    action: "VETO — Aja apenas no diferencial estético. Retorne o baseline para Radix padrão se aquilo não for um ícone 'Hero' da marca."

  evidence:
    - "[EXACT WORDS]: Se o Tailwind ou shadcn já resolve, use. Só customize o que é ÚNICO da marca. O que é único da Academia: Paleta monocromática + accent dourado... Cantos retos... Regra dos 8%."
```

## Decision Tree

```javascript
IF (overriding_core_ui_library_component)
  IF (override_is_purely_for_padding_or_minor_unbranded_whims == TRUE)
    THEN INITIATE_VETO
    THEN STRIP_OVERRIDE_ALLOW_RADIX_NATIVE ("Let the library maintain symmetry.")
  ELSE IF (override_is_needed_to_inject_Brand_Core_Gold_or_Monochrome)
    THEN ALLOW_OVERRIDE 
    THEN DELEGATE_TO_TAILWIND_CONFIG_VARIANTS 
      // Do it globally via CVA, never on the single element
```

## Failure Modes

### Frankenstein Shadcn Collapse
- **Trigger:** Ao instalar os Menus e Modais e achar o border-radius feio. Em vez de usar a varreduras root de variables `.globals.css` (Radius = 0), o bot espalha `rounded-none` estaticamente em 29 lugares diferentes.
- **Manifestation:** O arquivo de core do Shadcn fica monstruoso, impossível de atualizar na próxima versão do pacote via CLI; o design em dois dias descola e botões primários ficam com pontas e secudários redondos.
- **Detection:** Verificação do diff acusa manipulação nas bases do componente, ignorando `className` flexíveis.
- **Recovery:** Deleção dura do arquivo do componente alterado, rodar `npx shadcn-ui@latest add button` e recomeçar centralizando o `globals.css` das borderRadius.
- **Prevention:** Região bloqueada mentalmente: "Só toco no motor do Shadcn se for vida ou morte. Caso contrário, declaro na Rota e no Root."

## Integration with Workflow

```yaml
checkpoint:
  id: "visual-exclusivity-check"
  heuristic: AN_KE_053
  phase: "Component_Styling"

  validation_questions:
    - "Essa linha extra de CSS Tailwind aqui faria o criador oficial da biblioteca chorar? Eu preciso mesmo disto para transparecer a marca Alan?"
```

## Validation

**✓ Paradoxo Identificado:**
Customização visual é necessária para diferencial de marca, mas customização desenfreada compromete manutenibilidade de longo prazo.

**✓ Resolução Estabelecida:**
Whitelist explícita de chaves visuais sagradas (dourado, monocromático, cantos retos). Todas as demais customizações via configuração global Tailwind ou defaults Shadcn/Radix.

**✓ Critério de Sucesso:**
- Nenhum override em padding/margin de componentes base sem documentação
- 100% das customizações de marca centralizadas em `globals.css` ou CVA variants
- Diff futuro de `shadcn add` não conflita com overrides locais
