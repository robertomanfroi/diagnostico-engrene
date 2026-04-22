---
task-id: extract-implicit-analyze
name: "Deep Analysis Across 5 Axes"
version: 1.0.0
execution_type: Agent
model: Opus
model_rationale: "Deep analysis of tacit knowledge across 5 axes requires sustained reasoning with checkpoints and adversarial testing. Not Haiku-eligible."
haiku_eligible: false
estimated-time: 20 min
complexity: high

inputs:
  required:
    - scan_markers: "Lista de pontos marcados (output de extract-implicit-scan)"
    - source_corpus: "Conteudo original para re-consulta"
  optional:
    - prior_extractions: "Extracoes anteriores para triangulacao"

outputs:
  primary:
    - analysis_findings: "Achados classificados por eixo com evidencia, inferencia e impacto"

elicit: false
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: extract-implicit-analyze
  task_name: Deep Analysis Across 5 Axes
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 20m
  domain: Operational
  input:
  - '{''scan_markers'': ''Lista de pontos marcados (output de extract-implicit-scan)''}'
  - '{''source_corpus'': ''Conteudo original para re-consulta''}'
  - '{''prior_extractions'': ''Extracoes anteriores para triangulacao''}'
  output:
  - '{''analysis_findings'': ''Achados classificados por eixo com evidencia, inferencia
    e impacto''}'
  action_items:
  - Process All Markers Through the 5 Axes
  - Apply Axis-Specific Checks
  - Preserve the Core Distinctions
  - Emit Structured Findings
  - Run the Evidence Linking Gate
  acceptance_criteria:
  - All 5 axes analyzed with dedicated step per axis
  - Checkpoints applied (clareza, premissa raiz, formalizacao, evasao vs escopo)
  - Adversarial stress test applied to all evasion findings
  - 'Every CRITICO/ALTO finding includes `[SOURCE: minuto/pagina]` (VETO-EIM-003)'
  - Each finding formatted per axis output schema
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
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Deep Analysis Across 5 Axes

## Metadata

- **Parent:** `extract-implicit` | **Sequence:** Phase 2 of 5
- **Previous:** `extract-implicit-scan` | **Next:** `extract-implicit-prioritize`

## Purpose

Analyze each scan marker across 5 axes of implicit knowledge. Apply SECI Externalization (tacit to explicit) with checkpoints and adversarial stress tests.

## Prerequisites

- `extract-implicit-scan` completed with `scan_markers`
- Original `source_corpus` available for re-consultation

## Workflow / Steps

> **Foundation:** SECI Externalization (Nonaka & Takeuchi), Analytical/Syntopical levels (Adler).

### Step 1: Process All Markers Through the 5 Axes

For each `scan_marker`, classify and analyze it using the matrix below.

| Axis | Core Question | Mandatory Fields | Special Checkpoint |
|------|---------------|------------------|--------------------|
| Premissas | "Que suposicao nunca foi validada?" | `evidencia`, `assumido`, `impacto_se_falsa`, `pergunta_para_resolver` | Clareza + premissa raiz |
| Heuristicas | "Que regra pratica esta guiando a decisao?" | `padrao_observado`, `evidencia`, `por_que_importa`, `deveria_ser_formalizada`, `justificativa` | Deve ter `SE -> ENTAO` com trigger explicito |
| Pontos Cegos | "Que risco/dependencia nao foi discutido?" | `o_que_nao_foi_discutido`, `evidencia_da_ausencia`, `impacto_potencial`, `cenario_de_risco`, `pergunta_para_resolver` | Impacto concreto, nao abstrato |
| Decisoes Implicitas | "O que foi escolhido por omissao?" | `o_que_foi_escolhido_por_omissao`, `alternativas_nao_consideradas`, `evidencia`, `impacto`, `pergunta_para_validar` | Alternativas reais precisam ser nomeadas |
| Evasoes | "O que foi evitado, minimizado ou desviado?" | `tema_evitado`, `sinal_de_evasao`, `evidencia`, `tipo`, `implicacao`, `triangulacao` | Distinguir evasao de limite legitimo de escopo |

### Step 2: Apply Axis-Specific Checks

- **Premissas:** se nebulosa, reescreva em 1 frase; pergunte repetidamente "o que precisa ser verdade para isso existir?" ate chegar a raiz.
- **Heuristicas:** sem trigger explicito, nao e heuristica; reclassifique como observacao.
- **Pontos cegos:** sempre formular um `E se {situacao}?` com impacto verificavel.
- **Decisoes implicitas:** listar as alternativas ausentes, nao apenas dizer que houve omissao.
- **Evasoes:** aplicar steel man antes de acusar lacuna; so marcar como padrao forte se repetir em 3+ contextos e tocar tema central da expertise.

### Step 3: Preserve the Core Distinctions

- **Premissa Oculta:** o expert nao percebe que assume.
- **Ponto Cego:** o expert nao percebe que ignora.
- **Evasao Deliberada:** o expert percebe, mas evita abordar.

### Step 4: Emit Structured Findings

Use IDs por familia: `P-001`, `H-001`, `PC-001`, `D-001`, `EV-001`.

Minimal schema per finding:

```yaml
- id: "AXIS-001"
  nome: ""
  evidencia: "[SOURCE: minuto/pagina]"
  impacto: "CRITICO | ALTO | MEDIO"
  pergunta_para_resolver: ""
  detalhes_especificos_do_eixo: {}
```

### Step 5: Run the Evidence Linking Gate

Before finalizing, enforce VETO-EIM-003: every `CRITICO` or `ALTO` finding must include `[SOURCE: minuto/pagina]`. If any high-impact finding lacks evidence anchor, block the phase and repair the evidence first.

## Output

```yaml
analysis_findings:
  premissas:
    count: 0
    items: []
  heuristicas:
    count: 0
    items: []
  pontos_cegos:
    count: 0
    items: []
  decisoes_implicitas:
    count: 0
    items: []
  evasoes:
    count: 0
    items: []
  evidence_gate:
    all_critical_linked: true
    all_alto_linked: true
```

## Acceptance Criteria

- [ ] All 5 axes analyzed with dedicated step per axis [threshold: >= 5]
- [ ] Checkpoints applied (clareza, premissa raiz, formalizacao, evasao vs escopo) [threshold: >= 4]
- [ ] Adversarial stress test applied to all evasion findings [threshold: >= 1]
- [ ] Every CRITICO/ALTO finding includes `[SOURCE: minuto/pagina]` (VETO-EIM-003) [threshold: score >= 0.8]
- [ ] Each finding formatted per axis output schema [threshold: score >= 0.8]
- [ ] Evidence linking gate passed [threshold: score >= 0.8]

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-EIM-003 | Critical findings must be evidence-linked to source anchors | Verify each CRITICO/ALTO finding includes `[SOURCE: minuto/pagina]` | VETO - BLOCK. Reject until evidence anchors added. |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `extract-implicit.md` | Parent orchestrator |
| `extract-implicit-scan.md` | Previous phase (initial scan) |
| `extract-implicit-prioritize.md` | Next phase (prioritization) |

## Task Anatomy

- **Executor:** Agent
- **Inputs:** scan_markers; source_corpus
- **Outputs:** Achados classificados por eixo com evidencia, inferencia e impacto
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
