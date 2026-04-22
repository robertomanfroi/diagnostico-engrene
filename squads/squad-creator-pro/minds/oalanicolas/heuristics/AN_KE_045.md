# AN_KE_045 - Subtraction First Strategy

**Type:** Analytical Framework
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Ockham's Razor e Simplicidade Oculta
**Source:** [SOURCE: Extrações base do handoff do PKM v2 e modelamento central do Derek Sivers.]

## Purpose

Criar um atalho radical de eficiência cortando camadas burocráticas inteiras (workflows, apps e bots soltos). A intuição humana nativa sempre adiciona mais mecanismos para lidar com atrito; gênios resolvem problemas removendo as camadas defeituosas que os criam.

## Configuration

```yaml
AN_KE_045:
  name: "Subtraction First Strategy"
  zone: "genialidade"
  trigger: "Quando avaliando novos recursos, apps secundários, integrações ou o workflow diário da Base."

  rule: |
    SE você encontrar um gargalo burocrático, lento ou atritivo numa arquitetura ou modelo de conhecimento
    ENTÃO DESTRUA em vez de construir paliativos em cima. Pare de adicionar plugins e scripts de conserto; aplique "Subtract not Add".

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Subtração remove camadas de orquestração necessárias para paralelização efetiva, criando gargalo sequencial em arquiteturas distribuídas."
    resolution: "Validar pré-remoção: (1) alternativa sobrevive escalas futuras? (2) Não há conformidade/auditoria perdida? (3) Custo de re-arquitetar depois < custo mantendo stack atual? Se NÃO em qualquer, use SIMPLIFY ao invés de SUBTRACT."

  veto_condition:
    trigger: "Tentativa de resolver a complexidade de múltiplos calendários criando uma nova IA central de 'Sincronização entre Agendas'."
    action: "VETO — Force o corte radical. Remova 3 das agendas. Zere a variável na origem."

  evidence:
    - "[EXACT WORDS]: O que tira peso mental? 'Subtract not add' - Remove antes de adicionar ferramentas de 'manage' de peso mental. Useful not true - Foco em modelos úteis."
```

## Decision Tree

```javascript
IF (identifying_frictions_in_current_setup OR feeling_cognitive_overload)
  IF (solution_proposes_adding_new_tool == TRUE)
    THEN BLOCK_ADDITION
    THEN RUN_SUBTRACTION_AUDIT
      IF (can drop the entire process out of existence safely)
        THEN REMOVE_PROCESS
      ELSE
        THEN SIMPLIFY_DOWN_TO_BONE ("No plugins, plain text, single source.")
  ELSE
    // Directing towards native or zero-footprint approach
    THEN ALLOW_MODIFICATION
```

## Failure Modes

### Zumbis App-Stack
- **Trigger:** Com a desculpa de "Otimizar o Flow", instalar Zapier, Make e Notion para organizar pastas do macOS.
- **Manifestation:** Em menos de três semanas o sistema perde eficácia por não ser tolerante à bagunça. O indivíduo agora trabalha *para manter as ferramentas de produtividade*, e não para produzir.
- **Detection:** Reclamação explícita sobre a lentidão nos handoffs e loops gigantes do Agente ou o dono de negócio gastando 70% do tempo arrumando etiquetas no Notion.
- **Recovery:** Apagar as subcriaturas da stack, limpar a IA e retornar à base CLI/Text Puro.
- **Prevention:** Um gate de "Adição" que exige provar a impossibilidade de usar a Subtração.

## Integration with Workflow

```yaml
checkpoint:
  id: "subtraction-razor-gate"
  heuristic: AN_KE_045
  phase: "Architecture_Review"

  validation_questions:
    - "A próxima ferramenta vai introduzir um peso de manutenção eterno para resolver um atrito efêmero? Posso purgar a ação defeituosa?"
```

## Validation

**Paradox Check:** ✓ Identificado
- **Paradoxo:** Subtração cria fragilidade (plain text sem escala) vs. Adição cria complexidade (stack bloated).
- **Tensão Sistêmica:** Remover ferramentas de governança (auditoria, controle de acesso, versionamento) economiza peso mental *hoje* mas cria risco futuro.
- **Resolução:** Não é SUBTRACT vs. ADD. É SUBTRACT vs. SIMPLIFY vs. ADAPT. Use SUBTRACT apenas se validar escalabilidade da alternativa.
- **Evidência:** Zumbis app-stack (Notion pesado) vs. CLI puro sem histórico = dois extremos. O ponto ótimo está na *remoção seletiva*.

**Aplicabilidade:** Medium (funciona para workflows pessoais; requer guardrails para arquiteturas compartilhadas).
