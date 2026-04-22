<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: clone-mind-synthesis
  task_name: Clone Mind Synthesis
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Load Upstream Artifacts
  - Merge Into Clone Bundle
  - Prepare Validation Handoff
  acceptance_criteria:
  - Nenhuma fase anterior é reexecutada aqui [threshold: 0 re-executions]
  - Voice + Thinking DNA são consolidados num bundle único [threshold: >= 1 bundle]
  - O output fica pronto para smoke test e dashboard [threshold: >= 1 artifact]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
  coherence_threshold: 0.95
  error_behavior: raise
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Clone Mind Synthesis

**Task ID:** clone-mind-synthesis
**Version:** 1.0.0
**Purpose:** Sintetizar os artefatos já extraídos de fontes, Voice DNA e Thinking DNA em um bundle final de clone pronto para validação
**Orchestrator:** @oalanicolas
**Mode:** Synthesis-only

---

## Purpose

Esta task existe para a fase `synthesis-agent-block-generation` de `wf-clone-mind.yaml`.

Ela NÃO reexecuta:

- coleta de fontes;
- classificação OURO/BRONZE;
- extração de Voice DNA;
- extração de Thinking DNA.

Ela apenas consolida os artefatos já produzidos nas fases anteriores e gera o bundle final do clone.

---

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `sources_inventory` | file/object | Yes | Inventário validado de fontes |
| `voice_dna` | file/object | Yes | Artefato final de Voice DNA |
| `thinking_dna` | file/object | Yes | Artefato final de Thinking DNA |
| `mind_name` | string | Yes | Nome da mente clonada |
| `domain` | string | Yes | Domínio da mente |

---

## Workflow

### Step 1: Load Upstream Artifacts

Validar que `sources_inventory`, `voice_dna` e `thinking_dna` existem e pertencem ao mesmo `mind_name`.

### Step 2: Merge Into Clone Bundle

Gerar bundle final contendo:

- resumo de fontes;
- identidade e padrões de voz;
- frameworks, heurísticas e veto conditions;
- bloco consolidado pronto para agent generation;
- `fidelity_estimate` preliminar baseado nos artefatos existentes.

### Step 3: Prepare Validation Handoff

Emitir artefato final pronto para:

- smoke test comportamental;
- quality dashboard;
- eventual materialização do agente.

---

## Output

```yaml
output:
  primary:
    - clone_bundle
    - agent_block
  artifacts:
    - mind_dna_bundle.yaml
    - agent_block.md
    - synthesis_report.md
```

---

## Acceptance Criteria

- [ ] Nenhuma fase anterior é reexecutada aqui [threshold: 0 re-executions]
- [ ] Voice + Thinking DNA são consolidados num bundle único [threshold: >= 1 bundle]
- [ ] O output fica pronto para smoke test e dashboard [threshold: >= 1 artifact]

---

## Related Documents

- `workflows/wf-clone-mind.yaml` -- fase consumidora
- `tasks/an-extract-dna.md` -- referência histórica do monólito anterior

---

_Task Version: 1.0.0_
_Role: canonical synthesis contract for clone-mind workflow_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed clone-mind-synthesis output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above
