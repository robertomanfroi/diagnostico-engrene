---
task-id: an-extract-framework-analyze
name: "Source Classification & GAP Analysis"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Authenticity assessment and GAP analysis require deep semantic judgment."
haiku_eligible: false
estimated-time: 10 min
complexity: medium

inputs:
  required:
    - source: "Source material (interview, book, course, post, video)"

outputs:
  primary:
    - source_quality: "OURO or BRONZE classification with rationale"
    - gap_analysis: "Prometido vs Entregue with desvios espontaneos"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-framework-analyze
  task_name: Source Classification & GAP Analysis
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 10m
  domain: Operational
  input:
  - '{''source'': ''Source material (interview, book, course, post, video)''}'
  output:
  - '{''source_quality'': ''OURO or BRONZE classification with rationale''}'
  - '{''gap_analysis'': ''Prometido vs Entregue with desvios espontaneos''}'
  action_items:
  - Identify Source Type
  - GAP Analysis (Prometido vs Entregue)
  - Adversarial Test on GAP
  - Checkpoint -- GAP as Authenticity Signal
  acceptance_criteria:
  - Source classified as OURO or BRONZE with rationale
  - GAP analysis executed (prometido vs entregue)
  - Desvios espontaneos identified
  - Adversarial test applied to GAP
  - Authenticity signal assessed
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


# Task: Source Classification & GAP Analysis

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-extract-framework-analyze` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

- **Parent Task:** `an-extract-framework` (orchestrator stub)
- **Sequence:** Phase 1 of 3
- **Previous Task:** None
- **Next Task:** `an-extract-framework-trinity`

## Purpose

Classify source quality (OURO/BRONZE) and analyze the GAP between what the source promised and what it actually delivered, using deviations as signals of authentic thinking.

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AEF-001 | Source quality must be classified before extraction | BLOCK |

## Workflow / Steps

### Step 1: Identify Source Type

Ask: "Qual a fonte? (entrevista, livro, curso, post, video)"

Evaluate quality:
- OURO -- proceed with full extraction
- BRONZE -- warn that results will be limited, suggest finding gold

```yaml
checkpoint_autenticidade:
  question: "Fonte e autentica o suficiente para extrair Framework confiavel?"
  if_autentica: "Proceder com extracao completa"
  if_nao: "Avisar limitacao, sugerir buscar ouro"
  rationale: "Framework de fonte scripted = framework generico, nao do expert."
```

### Step 2: GAP Analysis (Prometido vs Entregue)

Analyze the DISTANCE between what the source promises and what it actually delivers.

**Questions:**
- "O que o expert DISSE que ia ensinar vs o que REALMENTE ensinou?"
- "Onde o conteudo desviou da promessa original?"
- "Que temas surgiram espontaneamente (nao planejados)?"

```yaml
gap_analysis:
  fonte: "{nome da fonte}"
  prometido: "{o que disse que seria o tema}"
  entregue: "{o que realmente foi discutido}"
  gap_size: "ALTO | MEDIO | BAIXO"
  desvios_espontaneos:
    - desvio: "{para onde foi}"
      sinal: "{o que revela sobre o pensamento real}"
  implicacao: "{o que o gap diz sobre autenticidade}"
```

### Step 3: Adversarial Test on GAP

```yaml
adversarial_gap:
  steel_man: "E se o gap e INTENCIONAL? Expert conscientemente mudou o plano."
  attack: "E se e simplesmente DESORGANIZACAO? Expert divagou sem proposito."
  test: "Desvio levou a framework/insight ou levou a nada?"
  verdict: "autentico | desorganizacao"
```

### Step 4: Checkpoint -- GAP as Authenticity Signal

```yaml
checkpoint_gap_analysis:
  question: "O gap entre prometido e entregue revela pensamento REAL ou indica fonte scripted?"
  if_gap_alto: "Fonte mais autentica — desvios sao ouro. Priorizar extracao dos desvios."
  if_gap_baixo: "Fonte possivelmente scripted — rebaixar para BRONZE se outros sinais confirmarem."
```

## Output

```yaml
source_quality: "OURO|BRONZE"
source_quality_rationale: ""
gap_analysis: { prometido, entregue, gap_size, desvios }
adversarial_verdict: "autentico|desorganizacao"
```

## Acceptance Criteria

- [ ] Source classified as OURO or BRONZE with rationale
- [ ] GAP analysis executed (prometido vs entregue)
- [ ] Desvios espontaneos identified
- [ ] Adversarial test applied to GAP
- [ ] Authenticity signal assessed

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-extract-framework.md` | Parent orchestrator |
| `an-extract-framework-trinity.md` | Next phase |
