---
task-id: etd-extract-and-classify
name: "ETD Phase 2: Extract & Classify (10 Categories + Epistemic Gate)"
version: 2.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Extracao com 10 categorias L4 e classificacao epistemica integrada requer sintese profunda"
estimated-time: 30 min
complexity: high
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
    - sources: "Fontes validadas com metodologia documentada"
    - recognition_patterns: "Output da Phase 1 (Discovery)"
    - frameworks: "Output da Phase 1 (Discovery)"

outputs:
  primary:
    - classified_candidates: "Candidatos aceitos com evidence_type, confidence, source_trace"
    - discarded_candidates: "Candidatos rejeitados com motivo explicito"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-extract-and-classify
  task_name: 'ETD Phase 2: Extract & Classify (10 Categories + Epistemic Gate)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 30m
  domain: Operational
  input:
  - "{'mind_name': 'Nome do expert'}"
  - "{'sources': 'Fontes validadas'}"
  - "{'recognition_patterns': 'Output Phase 1'}"
  - "{'frameworks': 'Output Phase 1'}"
  output:
  - "{'classified_candidates': 'Aceitos com evidence_type + confidence + source_trace'}"
  - "{'discarded_candidates': 'Rejeitados com motivo'}"
  action_items:
  - Extrair candidatos brutos usando 10 categorias L4
  - Classificar evidence_type e confidence de cada candidato
  - Aplicar Filtro de Distintividade (Teste dos 200 Founders)
  - Executar Auditoria de Fidelidade
  - Descartar genericos com motivo explicito
  acceptance_criteria:
  - 10 categorias L4 varridas
  - 8+ candidatos brutos extraidos
  - 100% classificados com evidence_type e confidence
  - Zero genericos aceitos
  - Source trace com minimo 2 fontes por aceito
  output_persistence: transient_output
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
  pre_condition: "Phase 1 (etd-discovery) completada com recognition_patterns e frameworks."
  post_condition: "Candidatos extraidos, classificados e filtrados. Prontos para consolidacao."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# ETD Phase 2: Extract & Classify

> **Objetivo:** Numa unica passagem: (A) extrair candidatos a heuristicas usando 10 categorias L4,
> depois (B) classificar epistemicamente e filtrar genericos. Saem apenas os que passaram no
> Teste dos 200 Founders com evidence_type, confidence e source_trace.
>
> **Principio:** NAO estamos resumindo ideias. Estamos extraindo PADROES REAIS de decisao,
> distinguindo o que e explicito do que e inferido, e eliminando generalidades.
>
> **Tempo estimado:** 30 minutos (20 extracao + 10 classificacao)

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EC-001 | All heuristics must be traceable to source evidence | Validate each has non-empty source field | VETO - BLOCK. Remove unsourced entries. |
| VETO-EC-002 | Zero invented heuristics | Cross-reference against source material | VETO - DISCARD candidate. |
| VETO-EC-003 | Zero generic candidates accepted | Apply 200 Founders Test | VETO - DISCARD. If it applies to 200 founders, it's generic. |

---

## PART A: EXTRACTION (10 Categories L4)

Extraia candidatos usando as 10 categorias canonicas. Aplique TODAS a cada fonte:

### Categoria 1: Principios Explicitos
Regras que o expert DECLAROU verbalmente ou por escrito.
- "Que principios ele repete em entrevistas, livros, discursos?"

### Categoria 2: Criterios Recorrentes de Decisao
- "Que metricas ou sinais ele SEMPRE verifica antes de decidir?"

### Categoria 3: Vetos Recorrentes (Deal-Breakers)
- "Que sinais fazem ele PARAR ou REJEITAR algo imediatamente?"

### Categoria 4: Tolerancias e Intolerancias
- "O que ele TOLERA que a maioria nao tolera?"
- "O que ele e INTOLERANTE sobre que a maioria ignora?"

### Categoria 5: Nocoes de Risco
- "Em que situacoes arrisca mais? Quando fica conservador?"

### Categoria 6: Trade-offs Preferidos
- "Velocidade vs qualidade — o que ganha?"
- "Curto prazo vs longo prazo — como balanceia?"

### Categoria 7: Padroes de Acao Repetidos
- "Que comportamentos aparecem em MULTIPLAS decisoes documentadas?"

### Categoria 8: Padroes de Nao-Acao
- "Que praticas comuns da industria ele rejeita?"

### Categoria 9: Frases Centrais que Codificam Visao de Mundo
- "Que frase dele, se entendida profundamente, explica 10+ decisoes?"

### Categoria 10: Decisoes Concretas que Revelam Heuristicas Implicitas
- "Que decisoes concretas revelam uma regra que ele nunca formulou explicitamente?"

**Formato de cada candidato bruto:**
```yaml
raw_candidate:
  id: "CANDIDATE_{NNN}"
  name: "Nome da heuristica"
  category_l4: "1-10"
  type: "decision|veto|prioritization"
  description: "Descricao breve do mecanismo"
  preliminary_source:
    - source: "Nome da fonte"
      evidence: "Citacao ou evidencia"
```

---

## PART B: CLASSIFICATION (Exit Gate)

Para CADA candidato bruto, aplique os 3 filtros em sequencia:

### B.1: Classificacao Epistemica

| Categoria | Descricao | Forca |
|-----------|-----------|-------|
| `explicit_statement` | Expert declarou isso explicitamente | Maxima |
| `repeated_pattern` | Padrao consistente em multiplas decisoes | Alta |
| `first_principles_inference` | Inferivel com forca de multiplos padroes | Media |
| `biographical_pattern` | Emerge da narrativa biografica | Baixa |

### B.2: Filtro de Distintividade (Teste dos 200 Founders)

4 perguntas — se QUALQUER falha, DISCARD:

1. **E DISTINTIVA** deste expert especifico? (nao generica)
2. **E operacionalizavel** em decisao real? (nao apenas insight)
3. **NAO e cliche** de produtividade/autoajuda?
4. **Tem substancia** para trigger + rule + veto + failure modes?

**Descartar imediatamente:**
- Conselho universal disfarçado de insight pessoal
- Cliché de produtividade
- Frase motivacional sem mecanismo
- Abstracao sem estrutura operacional
- Duplicata de candidato mais forte

### B.3: Auditoria de Fidelidade (5 Perguntas)

Para cada candidato que sobreviveu, responda HONESTAMENTE:

1. Esta heuristica e REALMENTE desta pessoa?
2. Aparece EXPLICITAMENTE ou por padrao CONSISTENTE?
3. NAO poderia pertencer a qualquer pessoa generica?
4. Ha evidencia suficiente para trigger, rule, veto E failure modes?
5. NAO estou preenchendo lacunas com imaginacao?

**Se qualquer resposta for "nao":** reduza escopo ou descarte.

### B.4: Atribuir Confidence e Source Trace

Para cada ACEITO:

```yaml
classified_candidate:
  id: "CANDIDATE_{NNN}"
  name: ""
  evidence_type: "explicit_statement|repeated_pattern|first_principles_inference|biographical_pattern"
  confidence: "high|medium|low"
  source_trace:
    - source: ""
      evidence: ""
      type: "quote|pattern|decision|inference"
  verdict: "ACCEPT"
```

Para cada DESCARTADO:
```yaml
discarded_candidate:
  id: "CANDIDATE_{NNN}"
  name: ""
  verdict: "DISCARD"
  discard_reason: "generic|abstract|redundant|biographical_only|motivational|insufficient_evidence"
```

---

## Output

Entregue:
1. Lista de candidatos ACEITOS com evidence_type, confidence, source_trace
2. Lista de candidatos DESCARTADOS com motivo explicito
3. Contagem: total extraidos / aceitos / descartados

**Elicit:** Apresente resumo aceitos/descartados para validacao antes de prosseguir.

---

## Quality Check

- [ ] 10 categorias L4 varridas
- [ ] 8+ candidatos brutos extraidos
- [ ] 100% classificados com evidence_type
- [ ] 100% aceitos tem confidence level
- [ ] Zero genericos aceitos (Teste dos 200 Founders)
- [ ] Source trace com minimo 2 fontes por aceito
- [ ] Descartados tem motivo explicito

**Score minimo:** 6/7 items checked

## Acceptance Criteria

- [ ] Extracao + classificacao numa unica passagem
- [ ] Zero candidatos genericos aceitos
- [ ] Source trace verificavel com minimo 2 fontes por aceito
- [ ] 100% classificados com evidence_type e confidence
