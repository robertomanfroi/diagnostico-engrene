# AN_KE_062 - Explicit Nature Declaration
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões sinkra-hub f5cce682 (sinkra-chief meeting), 156cf1df (CodeRabbit brownfield)]

## Purpose

Toda interação com squad/processo DEVE começar declarando explicitamente a NATUREZA do trabalho. São exatamente 3 naturezas — não um espectro, não um híbrido. A sessão f5cce682 revelou que sem essa declaração, o sinkra-chief assume standalone por default e o pipeline inteiro roda no escopo errado. O fix não foi "comunicar melhor" — foi criar templates com campo obrigatório ("Contexto: brownfield" como campo explícito no prompt). A sessão 156cf1df prova adoção real: "*map-process modo brownfield para CodeRabbit" — a declaração virou parte natural do comando.

## Configuration

```yaml
AN_KE_062:
  name: "Explicit Nature Declaration"
  zone: "excelencia"
  trigger: "Iniciando trabalho com squad, processo, ou sistema que pode ter múltiplas naturezas."
  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Clareza Upfront de Natureza"
    resolution: "Declarar apenas a natureza do trabalho (3 categorias mutualmente exclusivas), não inferir escopo. Maximize clareza na triagem inicial para minimizar retrabalho."

  rule: |
    SE iniciando trabalho com squad ou processo
    ENTÃO declarar natureza EXPLICITAMENTE como campo obrigatório:
      (1) standalone — squad/processo novo do zero
      (2) brownfield — refatorando/melhorando squad/processo existente
      (3) upgrade-pack / overlay — adicionando camada sobre base existente
    Sem declaração → chief assume standalone → pipeline inteiro no escopo errado.
    A declaração é CAMPO no template, não comunicação informal.

  veto_condition:
    trigger: "Iniciar pipeline/comando sem campo de natureza, ou natureza ambígua ('meio brownfield, meio standalone')."
    action: "VETO — 'Se o caso for um upgrade-pack, você precisa dizer isso logo no início.' Declare: standalone, brownfield, ou upgrade-pack. Sem isso, BLOCK."

  evidence:
    - "[SOURCE: sessão f5cce682, sinkra-hub] 'Se o caso for um upgrade-pack/DLS, você precisa dizer isso logo no início. Senão o chief pode assumir squad independente. Então sempre explicite uma destas 3 naturezas: standalone squad, brownfield de squad existente, upgrade-pack / overlay de um squad base'"
    - "[SOURCE: sessão f5cce682, sinkra-hub] Templates práticos criados com nature declaration obrigatória no prompt: 'Contexto: brownfield' como campo explícito"
    - "[SOURCE: sessão 156cf1df, sinkra-hub] '*map-process modo brownfield para CodeRabbit Automated Code Review' — aplicação prática em comando real"
```

## Decision Tree

```javascript
IF (starting_squad_or_process_work)
  REQUIRE: explicit nature declaration BEFORE any work begins

  STEP_1: DECLARE nature (obrigatório, campo no template)
    OPTION_1: "standalone" → full pipeline from scratch
      - All 7 SINKRA phases execute
      - No existing artifacts to merge with
    OPTION_2: "brownfield" → analyze existing, identify gaps, patch
      - Read existing squad FIRST
      - Map what exists vs what's missing
      - Merge strategy: preserve existing + fill gaps
    OPTION_3: "upgrade-pack" → create overlay layer
      - Base squad is READ-ONLY
      - Overlay adds capability without modifying base
      - Dependency on base is explicit

  STEP_2: VALIDATE nature makes sense
    IF (nature = standalone BUT existing squad found) → WARN: "brownfield detected, confirm standalone?"
    IF (nature = brownfield BUT no existing artifacts) → WARN: "nothing to brownfield, confirm standalone?"
    IF (nature = upgrade-pack BUT base squad not specified) → ERROR: "upgrade-pack requires base squad name"

  STEP_3: CONFIGURE pipeline for nature
    standalone → full 7-phase SINKRA pipeline
    brownfield → gap analysis first, then targeted phases
    upgrade-pack → overlay structure, base-compatible output

  IF (nature_not_declared)
    ASK: "Qual a natureza? standalone, brownfield, ou upgrade-pack?"
    BLOCK: until answer received
  NEVER: infer nature from context — always require explicit declaration
  FORMAT: field in template/command, not conversational mention
```

## Failure Modes

### O Chief que Assumiu Errado
- **Trigger:** Pedido de "criar squad para CodeRabbit" sem declarar que é brownfield de squad existente.
- **Manifestation:** sinkra-chief roda 7 phases de standalone. Gera squad completo que ignora o existente. Retrabalho para merge manual.
- **Detection:** Output do pipeline não referencia artefatos existentes quando deveria.
- **Prevention:** Campo obrigatório no template. Sessão 156cf1df mostra o padrão correto: "*map-process **modo brownfield** para CodeRabbit".

### A Natureza Híbrida
- **Trigger:** "É meio standalone, meio brownfield" — ambiguidade de escopo.
- **Manifestation:** Pipeline alterna entre criar do zero e referenciar existente, gerando artefatos inconsistentes.
- **Detection:** Output contém mix de novo + referências parciais a existente.
- **Prevention:** As 3 naturezas são MUTUAMENTE EXCLUSIVAS. Forçar escolha: se tem base existente → brownfield ou upgrade-pack, nunca "meio standalone".

## Validation

**Checklist de Implementação:**
- [ ] Campo "nature" é obrigatório no template de inicio de trabalho (standalone | brownfield | upgrade-pack)
- [ ] Sinkra-chief valida natureza antes de executar pipeline
- [ ] Se brownfield: gap analysis executado antes de outras fases
- [ ] Se upgrade-pack: base squad especificado e referência explícita mantida
- [ ] Se natureza não declarada: pipeline bloqueado com mensagem clara pedindo declaração
- [ ] Sessão f5cce682 e 156cf1df demonstram adoção em produção
- [ ] Comando real segue padrão: "*map-process modo {natureza} para {objetivo}"
- [ ] Nenhuma inferência de natureza a partir de contexto — sempre explícito
