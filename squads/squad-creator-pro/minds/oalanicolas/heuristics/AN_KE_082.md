# AN_KE_082 - Read Documentation Before Acting
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos — "leia antes de continuar" repetido cross-project]

## Purpose

A IA tende a AGIR imediatamente ao receber comando. Alan consistentemente FREIA e manda ler docs/papers/specs ANTES de executar. Entender o contexto previne 80% dos erros de implementação.

## Configuration

```yaml
AN_KE_082:
  name: "Read Documentation Before Acting"
  zone: "excelencia"
  trigger: "IA propondo executar algo em domínio que tem documentação disponível."

  rule: |
    SE existe documentação/spec/paper sobre o que vai ser feito
    ENTÃO ler PRIMEIRO, agir DEPOIS.
    "leia a documentação que criamos sobre tools, antes de avançarmos"
    Distinto de AN_KE_086 (verify state): este é sobre DOCUMENTAÇÃO, não estado de DB.

  evidence:
    - "[SOURCE: sessão 9c7751dc] 'leia a documentacao que criamos sobre tools, antes de avançarmos'"
    - "[SOURCE: sessão a8145c99] 'eu escrevi um paper sobre isso, quero que leia antes de continuarmos'"
    - "[SOURCE: sessão 4af01fc6] 'podemos capturar uma documentacao que mereça ser lida antes de fazer uma nova view em db'"

  sys_tension:
    - tension_with: "AN_KE_017 (Research No Meio, Não No Início)"
      resolution: "AN_KE_082 obriga leitura de docs ANTES de agir em domínios documentados; AN_KE_017 adia research para fase intermediária. Coexistem: ler docs conceituais no início (AN_KE_082) + defer deep research para meio do projeto (AN_KE_017)."
    - tension_with: "AN_KE_086 (Verify State Before Proceeding)"
      resolution: "AN_KE_082 governa documentação conceitual; AN_KE_086 governa estado de runtime. Ambas coexistem: ler docs + verificar estado = segurança total."
    - tension_with: "AN_KE_001 (Autonomy & Decisiveness)"
      resolution: "Leitura de docs não paralisa decisão — acelera ela. Docs informam melhor decisão. Paradoxo resolvido via: 'ler faz parte de agir bem.'"
```

## Decision Tree

```javascript
IF (about_to_implement_something)
  CHECK: does documentation/spec/paper exist for this domain?
    IF (YES) → READ it FIRST, then implement
      IF (doc contradicts plan) → ADJUST plan to align with doc
      IF (doc confirms plan) → PROCEED with confidence
    IF (NO) → CHECK: should documentation be created first?
      IF (complex domain) → CREATE minimal doc/spec BEFORE coding
      IF (simple change) → PROCEED directly
  NEVER: implement complex domain logic without reading existing docs
  NEVER: create DB views/tables without reading schema documentation
```

## Failure Modes

### A Migration que Ignorou o Paper
- **Trigger:** IA implementa tier system em banco sem ler paper escrito por Alan sobre como tiers devem funcionar.
- **Manifestation:** Schema implementado não reflete modelo conceitual do paper. Retrabalho completo.
- **Detection:** Output diverge de documentação existente.
- **Prevention:** "leia o paper antes de continuarmos," "leia a documentação que criamos sobre tools."

## Validation

**Checklist de Aplicação (AN_KE_082):**

- [ ] Documentação/spec/paper relevante foi identificada?
- [ ] Leitura completa foi feita ANTES de qualquer implementação?
- [ ] Plano foi ajustado para alinhar com conceitos da documentação?
- [ ] Divergências foram mapeadas e discutidas?
- [ ] Paradoxo com autonomia foi resolvido via "ler é agir bem"?
- [ ] Harmonia com AN_KE_086 (state verification) mantida?

**Status:** ✅ Heurística validada com sys_tension resolvida.