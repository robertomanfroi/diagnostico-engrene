---
task-id: an-assess-sources
name: "Assess Sources"
version: 3.0.0
execution_type: Orchestrator
model: Haiku
model_rationale: "Orchestrator stub — delegates to 2 sub-tasks. Haiku for routing."
haiku_eligible: true
note: "De-atomized from v2.0.0 (4 subtasks) to 2 subtasks. Merged score+prioritize+output into score."
estimated-time: 30 min
complexity: medium

specialist: "@oalanicolas"
specialist_guidance: |
  Use DNA Mental source assessment methodology:
  - 25 binary checkpoints across 5 dimensions (Autenticidade, Profundidade, Atualidade, Unicidade, Completude)
  - Mechanical tier classification (Crown Jewel / Ouro / Mixed / Bronze)
  - Worker script handles scoring deterministically; LLM for interpretation only
  - For complex assessment, invoke: @oalanicolas *assess-sources

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
  optional:
    - sources_dir: "Caminho para diretorio com fontes baixadas"

outputs:
  primary:
    - source_assessment: "Source map YAML completo com checkpoints, tiers, recommendations e gaps"

load: "data/an-source-tiers.yaml"
elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-assess-sources
  task_name: Assess Sources
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 35m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''sources_dir'': ''Caminho para diretorio com fontes baixadas''}'
  output:
  - '{''source_assessment'': ''Source map YAML completo com checkpoints, tiers, recommendations
    e gaps''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Todas as fontes listadas e catalogadas
  - Cada fonte avaliada com 25 checkpoints binarios
  - Tier calculado por media das 5 dimensoes
  - Crown Jewel identificado (se houver)
  - Prioridade de extracao definida
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


# Assess Sources

**Command:** `*assess-sources`

> **Principio:** "SCORE O QUE EXISTE, nao o que falta. Tier classification e MECANICA, nao subjetiva."

---

## Pipeline (2 Sub-Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `an-assess-sources-collect` | Collect Sources | 10 min |
| 2 | `an-assess-sources-score` | Score, Prioritize & Generate Source Map | 20 min |

---

## Execution Flow

```
an-assess-sources-collect
  | raw_sources_list
  v
an-assess-sources-score
  | source_assessment (FINAL OUTPUT)
  v
[DONE]
```

---

## Canonical Owner

This stub remains the backward-compatible entrypoint for direct task invocation.
The canonical owner of the atomic execution flow is:

- `workflows/wf-assess-sources.yaml`

---

## Worker Script

When sources are downloaded as local files, the worker script MUST run first:

```
bash squads/squad-creator-pro/scripts/assess-sources.sh <sources-dir> > /tmp/preflight-assess-sources.yaml
```

The script scores all 25 checkpoints per source deterministically. The LLM role is interpretation only (Phase 2).

---

## Veto Conditions (Consolidated)

| ID | Condition | Phase | Result |
|----|-----------|-------|--------|
| VETO-AS-001 | `mind_name` must be provided | Phase 1 | BLOCK |
| VETO-AS-002 | Source fragmentation detected | Phase 1 | BLOCK |
| VETO-AS-003 | Worker script available but not executed | Phase 2 | BLOCK |
| VETO-AS-004 | Subjective scoring override without evidence | Phase 2 | BLOCK |
| VETO-AS-005 | Subjective override of mechanical tier | Phase 2 | BLOCK |
| VETO-AS-006 | Crown Jewel criteria met but not applied | Phase 2 | BLOCK |
| VETO-AS-007 | Feedback loop reclassification without evidence | Phase 2 | BLOCK |
| VETO-AS-008 | Opinion-based tier override in feedback loop | Phase 2 | BLOCK |

---

## Completion Criteria

- [ ] Todas as fontes listadas e catalogadas
- [ ] Cada fonte avaliada com 25 checkpoints binarios
- [ ] Tier calculado por media das 5 dimensoes
- [ ] Crown Jewel identificado (se houver)
- [ ] Prioridade de extracao definida
- [ ] Source map YAML gerado com checkpoints detalhados
- [ ] Gaps identificados para busca de fontes adicionais
- [ ] Post-Extraction Feedback Loop executado (se extracao ja foi feita)

---

**Squad Creator Pro | Source Assessor v3.0**

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name
- **Outputs:** Source map YAML completo com checkpoints, tiers, recommendations e gaps
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] Todas as fontes listadas e catalogadas
- [ ] Cada fonte avaliada com 25 checkpoints binarios
- [ ] Tier calculado por media das 5 dimensoes
- [ ] Crown Jewel identificado (se houver)
- [ ] Prioridade de extracao definida
- [ ] Source map YAML gerado com checkpoints detalhados
- [ ] Gaps identificados para busca de fontes adicionais
- [ ] Post-Extraction Feedback Loop executado (se extracao ja foi feita)
