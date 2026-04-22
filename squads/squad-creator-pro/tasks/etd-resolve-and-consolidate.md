---
task-id: etd-resolve-and-consolidate
name: "ETD Phase 3: Resolve & Consolidate (Conflict + Deduplication)"
version: 2.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Resolver conflitos e consolidar mecanicas similares requer avaliacao estrutural complexa"
estimated-time: 20 min
complexity: high
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - classified_candidates: "Output da Phase 2 (Extract & Classify) — apenas candidatos aceitos"

outputs:
  primary:
    - consolidated_deck: "Deck deduplicado com tensoes mapeadas e ranqueado"
    - tension_synergy_map: "Mapa isolado de relacoes (conflitos irresolviveis e sinergias)"
    - merge_log: "Log de decisoes de resolucao e absorcao"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-resolve-and-consolidate
  task_name: 'ETD Phase 3: Resolve & Consolidate (Conflict + Deduplication)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 20m
  domain: Operational
  input:
  - "{'mind_name': 'Nome do expert'}"
  - "{'classified_candidates': 'Output Phase 2'}"
  output:
  - "{'consolidated_deck': 'Deck deduplicado e ranqueado'}"
  - "{'tension_synergy_map': 'Mapa de tensoes e sinergias'}"
  - "{'merge_log': 'Decisoes de resolucao explicadas'}"
  action_items:
  - Detectar heuristicas que se contradizem ou sao semanticamente redundantes
  - Resolver contradicoes pelo Protocolo de 4 Prioridades (recurrence, maturity, concrete, operational)
  - Fazer merge de variacoes redundantes no card mais forte (deduplicacao)
  - Preservar tensoes genuinas como 'tension_with'
  - Ranquear o deck consolidado (evidence, recurrence, applicability) e atribuir Zonas (0.8, 4, 20)
  acceptance_criteria:
  - Zero duplicatas semanticas (variacoes do mesmo mecanismo aglutinadas)
  - Todas as contradicoes foram resolvidas ou preservadas intencionalmente como tension
  - consolidated_deck restrito aos outputs logicamente unicos
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "Phase 2 (etd-extract-and-classify) concluida com candidatos aprovados e limpos de genericos."
  post_condition: "Conflitos limpos e sistema consolidado. Pronto para transformacao em Decision Cards L4."
  performance: "executar SLA declarado, aplicar prioridades de maneira analitica."
```
<!-- SINKRA_CONTRACT:END -->


# ETD Phase 3: Resolve & Consolidate

> **Objetivo:** Auditar a lista de candidatos provados para eliminar contradicoes falhas (atraves do protocolo de resolucao) e redundancias semanticas (merge). O que sobrevive e ranqueado por potencia.
>
> **Principio Central:** "Nunca mantenha 2 cards que sao variacoes do mesmo mecanismo cognitivo com fardas diferentes. Melhore o card vencedor com a fracao de inteligencia do perdedor."
>
> **Tempo estimado:** 20 minutos

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-RC-001 | Zero redundancias semanticas | Compare mechanism between cards, not just names | VETO - MERGE. Absorb weaker card into stronger. |
| VETO-RC-002 | Card count cap | Count final accepted cards | VETO - CONSOLIDATE. If > 20, force-merge weaker variations. |

---

## Step 1: Deteccao de Conflitos e Protocolo de 4 Prioridades

Cruze todas as heuristicas aceitas. Para contradicoes abertas (A diz agir rapido, B diz ser devagar), aplique o filtro de prioridade a seguir **em ordem**:

1. **Recurrence (Padrao Recorrente):** O que ele faz NA MAIORIA das vezes ganha.
2. **Maturity (Maturidade temporal):** Se uma visao e mais recente (ex: pos-pandemia vs pre-2010), a visao madura vence. (Antigo vai para Notes).
3. **Concrete Action over Theory:** A acao verificavel no mundo real supera a frase inspiracional dita ao jornalista.
4. **Operational Status:** Se A e praticavel (tem formula) e B e apenas lamento abstrato, A absorve B.

**Se NENHUM criterio resolver** \u2192 A contradicao e uma TENS\u00c3O GENU\u00cdNA. O perito convive com isso. Documente em `tension_map`.

---

## Step 2: Deteccao de Redundancia e Merge

Heuristicas que ensinam a **MESMA alavanca** sob angulos diferentes devem ser aglutinadas.
- **Sinal:** Ter o mesmo 'trigger' base e 'rule' fundamental apenas descritos com sinonimos.
- **Acao:** Abrace os insights laterais da versao mais fraca \u2192 Insira em "Notes"/ "Failure Modes" da versao dominante. Delete o id da fraca.

---

## Step 3: Construcao do Mapa de Tensoes e Sinergias

Registre as conjuncoes orbitais dos cards restantes:
```yaml
synergy_tension_map:
  tensions:
    - card_a: "{ID}"
      card_b: "{ID}"
      trade_off: "Como balancear o peso quando ambos contextos ocorrem"
  synergies:
    - card_a: "{ID}"
      card_b: "{ID}"
      pattern: "sequential|parallel|conditional"
```

---

## Step 4: Rankear por Qualidade e Atribuir Zonas L4

Determine a potencia relativa dos sobreviventes usando 5 dimensoes:
*(Distintividade, Recorrencia, Poder Explicativo, Pragmatismo, Centralidade ao Core)*

Com esse score imaginario, defina a Zone:
- **`zone_0.8` (Genialidade):** Core axioms; Os pilares inconfundiveis desse expert.
- **`zone_4` (Excelencia):** Heuristicas de otimizacao forte em situacoes rotineiras importantes.
- **`zone_20` (Impacto):** Regras colaterais que garantem eficiencia local.

---

## Output / Entregaveis

Entregue:
1. `consolidated_deck`: Lista de objetos limpos, com sua 'Zone', sem o lixo de redundancia repetitiva. `tension_with` e `synergy_with` populados nas metadatas.
2. `merge_log`: Descritivo breve demonstrando a 'conta matematica' mental que fez para aglutinar ou resolver conflitos em X situacoes.
3. `tension_synergy_map`: O arquivo isolado da dinamica em rede das regras.

---

## Quality Check

- [ ] Resolvidos os conflitos com uso da hierarquia de 4 prioridades
- [ ] Todas as redundancias mecanicas fundidas (zero duplicates)
- [ ] tension_with / synergy_with mapeado
- [ ] Ranking (Zonas) executado no topo do output

**Score minimo:** 4/4 items checked
