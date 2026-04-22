---
task-id: an-extract-framework-integrate
name: "Paradigm Inversions & Cross-Lens Integration"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Paradigm inversion detection and cross-lens integration require deep reasoning."
haiku_eligible: false
estimated-time: 15 min
complexity: medium

inputs:
  required:
    - source: "Source material"
    - gap_analysis: "From Phase 1"
    - playbook: "From Phase 2"
    - framework: "From Phase 2"
    - swipe_file: "From Phase 2"

outputs:
  primary:
    - paradigm_inversions: "Where expert inverts established paradigms"
    - cross_lens_map: "Integrated territory map across all lenses"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-framework-integrate
  task_name: Paradigm Inversions & Cross-Lens Integration
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 15m
  domain: Operational
  input:
  - '{''source'': ''Source material''}'
  - '{''gap_analysis'': ''From Phase 1''}'
  - '{''playbook'': ''From Phase 2''}'
  - '{''framework'': ''From Phase 2''}'
  - '{''swipe_file'': ''From Phase 2''}'
  output:
  - '{''paradigm_inversions'': ''Where expert inverts established paradigms''}'
  - '{''cross_lens_map'': ''Integrated territory map across all lenses''}'
  action_items:
  - Extract Paradigm Inversions
  - Adversarial Test on Inversions
  - Cross-Lens Integration Map
  - Validate Completeness
  acceptance_criteria:
  - Playbook has clear sequential steps
  - Framework has SE/ENTAO rules
  - Swipe File has REAL examples
  - The three complement each other
  - Cross-Lens Integration Map generated
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Paradigm Inversions & Cross-Lens Integration

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-extract-framework-integrate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `an-extract-framework` (orchestrator stub)
- **Sequence:** Phase 3 of 3
- **Previous Task:** `an-extract-framework-trinity`
- **Next Task:** None (final phase)

## Purpose

Extract paradigm inversions where the expert contradicts established field wisdom, apply adversarial testing, and integrate findings across all lenses into a cognitive territory map.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AEF-003 | Output must include all three Trinity legs with evidence | BLOCK |

## Workflow / Steps

### Step 1: Extract Paradigm Inversions

**Questions:**
- "Que crenca convencional do campo o expert REJEITA?"
- "Antes se pensava X -> o expert argumenta Y. Qual o raciocinio?"
- "Que 'verdade aceita' e tratada como erro?"

```yaml
paradigm_inversions:
  - id: "INV-001"
    conventional: "{o que o campo acredita}"
    expert_position: "{o que o expert defende}"
    reasoning: "{por que inverte}"
    evidence: "{citacao}"  # [SOURCE: pagina/minuto]
    hidden_framework: "SE {campo diz X} -> ENTAO {expert faz Y} PORQUE {razao}"
```

### Step 2: Adversarial Test on Inversions

```yaml
adversarial_inversion:
  steel_man: "Qual a versao MAIS FORTE desta inversao?"
  attack: "E se e EGO, nao insight? E se o campo mainstream esta CERTO?"
  test: "A inversao tem [SOURCE:] com raciocinio E evidencia?"
  survive_criteria:
    - "Raciocinio logico documentado"
    - "Evidencia de resultado (cases, numeros, dados)"
    - "Consistencia com outros frameworks do mesmo expert"
```

**Checkpoint:**

```yaml
checkpoint_inversao_real:
  question: "Isso e uma INVERSAO real de paradigma ou apenas reformulacao do obvio?"
  if_inversao: "Documentar com [SOURCE:] e extrair framework oculto"
  if_reformulacao: "Descartar — nao e insight, e ruido"
  rationale: "'Qualidade importa' nao e inversao. 'Volume e inimigo da qualidade' e."
```

### Step 3: Cross-Lens Integration Map

Integrate findings from all 3 lenses (GAP Analysis + Inversions + Evasion Scan):

```
GAP Analysis --> WHERE the expert thinks live
    |
    v
Paradigm Inversions --> WHAT the expert thinks differently
    |
    v
Evasion Scan --> WHERE the expert does NOT operate
```

**Integration questions:**
- "O expert desvia do script (GAP) PARA falar de que? Esse desvio contem inversao?"
- "Onde o expert inverte paradigma (confiante) vs onde evade (fragilidade)?"
- "O GAP mostra o expert indo para tema X. Mas ele EVADE tema Y. Relacao entre X e Y?"

```yaml
cross_lens_map:
  expert: "{nome}"
  territory_of_strength:
    description: "Onde o expert opera com confianca"
    evidence:
      - from_gap: "{desvio espontaneo que revelou inversao}"
      - from_inversion: "{paradigma invertido com confianca}"
  territory_of_avoidance:
    description: "Onde o expert NAO opera"
    evidence:
      - from_evasion: "{tema evitado}"
      - from_gap: "{tema prometido mas nao entregue}"
  boundary_insights:
    description: "O que a fronteira entre strength e avoidance revela"
    pattern: "{padrao observado}"
    implication_for_clone: "{como isso afeta o design do clone}"
  cross_source_signals:
    confirmed_patterns:
      - pattern: "{descricao}"
        sources: ["{fonte 1}", "{fonte 2}", "{fonte 3}"]
        confidence: "ALTA (3+ fontes) | MEDIA (2 fontes) | BAIXA (1 fonte)"
```

**Checkpoint:**

```yaml
checkpoint_integracao:
  question: "O mapa integrado revela algo NOVO que nenhuma lente sozinha mostrou?"
  if_novo: "Integracao real — insight emergente documentado"
  if_colagem: "Apenas juntou listas. Refazer perguntando: 'O que a FRONTEIRA revela?'"
```

### Step 4: Validate Completeness

- [ ] Playbook has clear sequential steps
- [ ] Framework has SE/ENTAO rules
- [ ] Swipe File has REAL examples
- [ ] The three complement each other
- [ ] Cross-Lens Integration Map generated
- [ ] At least 1 paradigm inversion extracted

```yaml
checkpoint_humble_expert:
  question: "Estou CONFIANTE no processo mas HUMILDE sobre o conteudo extraido?"
  if_sim: "Validacao com abertura para erro"
  if_nao: "Marcar pontos de incerteza como [NEEDS_VALIDATION]"
```

## Output

```yaml
paradigm_inversions: [{ id, conventional, expert_position, reasoning, evidence }]
cross_lens_map: { territory_of_strength, territory_of_avoidance, boundary_insights }
completeness_check: { all items validated }
```

## Acceptance Criteria

- [ ] At least 1 paradigm inversion extracted with [SOURCE:]
- [ ] Adversarial test applied to each inversion
- [ ] Cross-Lens Integration Map generated with territories
- [ ] Boundary insights documented
- [ ] Completeness validated (3 Trinity legs + lenses integrated)
- [ ] Uncertain points marked [NEEDS_VALIDATION]

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-extract-framework.md` | Parent orchestrator |
| `an-extract-framework-trinity.md` | Previous phase |
| `checklists/mental-model-integration-checklist.md` | Validation checklist |
