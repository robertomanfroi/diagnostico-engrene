---
task-id: etd-l4-card-generation
name: "ETD Phase 4: L4 Card Generation (Architecture + Failure Modes DUAL)"
version: 2.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Montar cards operacionais completos incluindo Source Trace e DUAL Failure Modes detalhados"
estimated-time: 25 min
complexity: high
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - sources: "Fontes validadas com metodologia documentada"
    - consolidated_deck: "Deck consolidado da Phase 3 (Resolve & Consolidate) com ranking organizadas"
    - tension_synergy_map: "Mapa de tensoes e sinergias preenchido"

outputs:
  primary:
    - decision_cards_yaml: "Registro YAML com estrutura completa dos cards (decision-cards.yaml)"
    - individual_cards: "Arquivos .md de heuristicas no formato L4 canonico completo"
    - decision_pipeline: "Pipeline global de tomada de decisao em niveis (Analysis, Options, Selection)"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-l4-card-generation
  task_name: 'ETD Phase 4: L4 Card Generation (Architecture + Failure Modes DUAL)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 25m
  domain: Operational
  input:
  - "{'consolidated_deck': 'Output da Phase 3 (deck deduplicado)'}"
  - "{'tension_synergy_map': 'Network links'}"
  output:
  - "{'decision_cards_yaml': 'DB YAML completo (L4 registry)'}"
  - "{'individual_cards': 'Ate 20 arquivos \".md\" separados'}"
  - "{'decision_pipeline': 'Fluxo global do expert'}"
  action_items:
  - Definir Arquitetura de Decisao raiz (decision_pipeline + risk_profile)
  - Converter Heuristicas Rankeadas (Phase 3) no formato Decision Card L4 canonico
  - Escrever secoes "Purpose" rigorosas (zero fluffy, focus pragmatics)
  - Absorver logs de Anti-Patterns originais gerando Failure Modes DUAL completos
  - Apensar evidencing blocks rigorosos de source
  acceptance_criteria:
  - Decision pipeline descreve os passos cognitivos reais ao abordar um problema central
  - Cada Decision Card (L4) contem failure modes Omission + Misapplication (Dual)
  - Cada Decision Card L4 contem Configuration (trigger + tension_with + synergy_with)
  - 100% dos Decision Cards contem Evidence_Type (epistemic fidelity)
  - Nenhum card individual quebra regras Categoria 10 sem notas anexadas
  output_persistence: individual_files_and_yaml
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: high
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "Phase 3 (Resolve & Consolidate) completada com deck finalistico L4."
  post_condition: "Decision Cards .md preenchidos junto ao map.yaml master global."
  performance: "Densa formatacao de Output; Nao resuma."
```
<!-- SINKRA_CONTRACT:END -->


# ETD Phase 4: L4 Card Generation

> **Objetivo:** Converter heuristicas consolidadas em Decision Cards L4 completos **E** mapear o pipeline de decisao global abstrato do expert.
>
> **Formato L4:** Purpose + Source Trace + Configuration + Decision Tree + Failure Modes (DUAL) + Notes
>
> **Principio Integrado:** A 'Phase Anti-Patterns' nativa nao e mais uma rotina a parte. Ela vive dentro da topologia rigorosa dos Failure Modes Duplos.
>
> **Tempo estimado:** 25 minutos

---

## Step 1: Decision Global Pipeline (Arquitetura Raiz do Expert)

Mapeie como o proprio expert abordaria e processaria a chegada de uma decisao complexa aleatoria, passo a passo logico.

```yaml
decision_pipeline:
  name: ""
  stages:
    - stage: "Input"
      action: "O que coleta primeiro ao receber um ticket de caos?"
    - stage: "Analysis"
      action: "O que elimina/filtra via Framework Phase 1?"
    - stage: "Selection"
      action: "Qual avaliacao critica o faz decidir (ou aplicar a Veto condition)?"
    - stage: "Validation"
      action: "Como audita a propria escolha? (Risk tolerance checks)"
```
**Decision Weights & Risk Profile:**
Indique o `risk_profile (tolerance, risk_seeking_domain, risk_mitigation)` global dele.

---

## Step 2: Gerar Decision Cards L4 Individuais

Para CADA heuristica do `consolidated_deck`, escreva um texto no formato a seguir para constituir o artefato markdown individual de arquivamento.

```markdown
# {ID} - {Nome da Heuristica}
**Type:** {Decision|Veto|Prioritization} Heuristic
**Zone:** {zone_0.8|zone_4|zone_20}
**Mind:** {Nome do Expert}
**Confidence:** {high|medium|low}
**Evidence Type:** {explicit_statement|repeated_pattern|first_principles_inference|biographical_pattern}

## Purpose
{4-6 linhas densas explicando o PROBLEMA que a heuristica resolve, QUANDO ela deve ser aplicada e POR QUE ela economiza tempo cognitivo. Sem autoajuda, apenas contexto.}

## Source Trace
{Para CADA fonte que sustenta esta heuristica, min: 1 principal + 1 paralela, da auditoria Phase 2:}
- **{Nome da fonte real}:** {Resumo da evidencia documentada}
- **{Nome da metrica cruzada}:** {Cross-logic inference}

## Configuration
\```yaml
{ID}:
  name: "Nome da Heuristica"
  zone: "zone_0.8|zone_4|zone_20"
  confidence: "high|medium|low"
  evidence_type: "explicit_statement|repeated_pattern|first_principles_inference|biographical_pattern"
  evidence_threshold: "{threshold mais honesto - e.x: hard_data}"
  trigger: "Condicao exata no ambiente para invocar (input de mercado)"
  tension_with: ["IDs extraidos em Resolve & Consolidate"]
  synergy_with: ["IDs mapeados em Resolve & Consolidate"]
  rule: |
    SE {contexto observado pelo expert}
    ENTAO {acao padrao e diretiva}
    NUNCA {a pior asneira padrao ignorada - anti-pattern principal}
  veto_condition:
    trigger: "O que seria um erro letal inaceitavel"
    action: "VETO - Pare tudo e elimine o vetor imediatamente."
  evidence:
    - "[SOURCE] 'citacao da Phase 2'"
\```

## Decision Tree
\```javascript
IF ({condicao_contextual_1})
  STEP_1: {avaliacao preliminar do pipeline root}
    IF ({sinal_verde}) -> {acao_proativa}
    ELSE IF ({red_flag}) -> {recuo_estrategico}
NEVER:
  {Ponto-cego que o expert executa veto}
\```

## Failure Modes
*(Mergidos a partir da logica de anti-patterns antigas. Desdobra a heuristica no tempo.)*

### Misapplication / Excess
*(Quando a organizacao tentar exagerar o culto e distorcer a regra para aplicacoes irrazoaveis. Falha por excesso.)*
- **Trigger:** {condicoes ou mal-entendido que causam desdobramento dogmatico}
- **Manifestation:** {como a disfuncao vaza nas metricas/ambiente}
- **Detection:** {rastros forenses para deteccao preventiva antes da catastrofe}
- **Recovery:** {o contrapeso tatico — rollback / tension override}
- **Prevention:** {pratica profilatica que modula acerto}

### Omission / Neglect
*(Quando a heuristica e obvia mas por comodidade ou medos culturais a empresa falha em evoca-la na hora de desespero.)*
- **Trigger:** {covardia, inercia de consenso cego ou bias}
- **Manifestation:** {os red flags estouram e sao aceitos como norma}
- **Detection:** {auditoria da operacao}
- **Recovery:** {gatilho manual para acordar a equipe}
- **Prevention:** {inibir esquecimento em processos corriqueiros}

## Notes
- Tensao documentada com: {ID} \u2192 Aprofundamento do trade-off validado.
- Limite critico de validade do 'First Principle' operante.
```

---

## Step 3: Gerar L4 Unified Registry (`decision-cards.yaml`)

Sumario index para programabilidade automatica.

```yaml
decision_cards:
  mind_slug: "{slug}"
  mind_name: "{name}"
  version: "1.0.0"
  total: 0
  generated_at: "{date}"
  generated_by: "decision-card-generator-L4"
  sources: []
  cards:
    - id: "{ID}"
      name: ""
      zone: "zone_0.8|zone_4|zone_20"
      confidence: "high|medium|low"
      evidence_type: "explicit_statement|repeated_pattern|first_principles_inference|biographical_pattern"
      evidence_threshold: ""
      tension_with: []
      synergy_with: []
      pipeline_instances: []
```

---

## Quality Check

- [ ] Arquitetura Raiz e Modelos de Risco definidos para todo o pipeline do perito
- [ ] TODOS os cards individuais (`.md`) com Source Trace explicita e metadados L4 validos
- [ ] TODOS os cards contemplam categoricamente a DUALIDADE de Failure Modes (Excess / Neglect) com 5 triches taticos
- [ ] Todos os blocos Configuration e Decision Trees livres de cliches pseudo-motivacionais
- [ ] Sumarizacao de Zonas e links com tensoes explicitados

**Score minimo:** 5/5 validos
