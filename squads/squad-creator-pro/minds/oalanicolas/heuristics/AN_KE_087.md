# AN_KE_087 - Brand Domain Isolation
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mentelendaria c5b4f186 + sessão extrai d28b9844 — contaminação entre marcas/projetos]

## Purpose

Nunca cruzar domínios de marca. Conceitos de um business (Thiago Finch/Outliers) NUNCA entram em documentos de outro (Academia Lendária). Configs de um projeto NUNCA contaminam templates de outro. Isolamento total entre universos de marca.

## Configuration

```yaml
AN_KE_087:
  name: "Brand Domain Isolation"
  zone: "excelencia"
  trigger: "Trabalhando com múltiplas marcas, projetos ou businesses que compartilham infraestrutura."

  rule: |
    SE múltiplas marcas/projetos compartilham repo ou ferramentas
    ENTÃO isolamento TOTAL de conteúdo entre domínios.
    NUNCA usar conceitos/nomes/termos de uma marca em documentos de outra.
    Configs de projeto A NUNCA poluem template de projeto B.

  veto_condition:
    trigger: "Conceitos de marca X aparecendo em documento de marca Y."
    action: "VETO — Limpar contaminação. Verificar se template está 'sujo' com refs de outro projeto."

  evidence:
    - "[SOURCE: sessão c5b4f186] 'Isso sao nomes que não são usados em nada pela academia lendária, isso é de Thiago Finch do movimento Outliers, não use de forma alguma Outlier, Bunda Mole e Mulambo em NENHUM documento da Academia Lendária'"
    - "[SOURCE: sessão d28b9844, extrai] 'revise se eles não estão sujos com configurações de outros projetos, quero deixar este como padrão AIOX sem referencia a projetos nao inclusos nesta estrutura'"

  sys_tension:
    tension_with: "AN_KE_007 (REUSE > CREATE) — eficiência através de reutilização"
    resolution: "Criar templates brand-neutral com abstração de configurações via variáveis; isolar context-specific references em branches/overrides per business"
```

## Decision Tree

```javascript
IF (working_with_multiple_brands_or_projects)
  STEP_1: IDENTIFY active brand context
    WHICH brand am I working on RIGHT NOW?
  STEP_2: SCAN for cross-contamination
    GREP: terms from brand A in docs of brand B
    CHECK: templates for refs to other projects
    CHECK: configs for values from other environments
  STEP_3: ON CONTAMINATION FOUND
    CLEAN: remove all foreign brand references
    VERIFY: template is "clean" — no refs to excluded projects
  NEVER: use Outliers/Mulambo terms in Academia Lendária docs
  NEVER: use project-specific configs in shared templates
```

## Failure Modes

### O Template Sujo
- **Trigger:** Template base usado em projeto A é copiado para projeto B sem limpeza.
- **Manifestation:** "revise se eles não estão sujos com configurações de outros projetos."
- **Detection:** `grep -ri 'outlier\|mulambo\|bunda.mole' workspace/businesses/academia-lendaria/`
- **Prevention:** Template audit antes de reusar. Cada template deve ser brand-neutral ou brand-specific.

## Validation

**Paradoxo Identificado:**
- **Tensão:** Maximizar eficiência através da reutilização de templates vs. garantir isolamento total entre domínios de marca
- **Resolução:** Implementar camada de abstração paramétrica (brand-agnostic templates + context-specific overrides)
  - Templates reutilizáveis devem usar placeholders: `{BRAND_NAME}`, `{PROJECT_CONFIG}`, `{CONTEXT_SCOPE}`
  - Cada negócio/marca fornece seu próprio arquivo de overrides: `workspace/businesses/{slug}/config/template-overrides.yaml`
  - Scripts de validação (pre-commit hooks) verificam contaminação cruzada automaticamente
  - Documentação explícita sobre qual template é "brand-neutral" vs "brand-specific"

**Critério de Sucesso:**
- Zero contaminação cruzada de conceitos/nomes entre documentos de diferentes marcas
- Reutilização eficiente de templates via parametrização
- Auditoria automatizada detecta violações em tempo de commit
