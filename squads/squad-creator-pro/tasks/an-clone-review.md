<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-clone-review
  task_name: Clone Review (Stub)
  status: pending
  responsible_executor: Worker
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Fontes avaliadas com checkpoints binarios
  - Trindade verificada (15 checkpoints total)
  - Estagios revisados com checkpoints
  - Quick fidelity com 5 checkpoints
  - Report com percentages e gaps especificos
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Clone Review (Stub)

**Command:** `*clone-review`
**Execution Type:** Hybrid (Worker script 90% + Agent interpretation 10%)
**Worker Script:** `scripts/clone-review.sh`
**Model:** `Haiku` (QUALIFIED -- 90% deterministic via script, Agent interprets pre-computed data only)
**Haiku Eligible:** YES
**Load:** `data/an-source-tiers.yaml`

## Purpose

Review completo de um clone existente: fontes, trindade, estagios, fidelidade. Equivalente a um audit geral.

---

## SCOPE DEFINITION (CRITICAL)

```yaml
scope_definition:
  principle: "Review clone = wrapper + TODOS arquivos referenciados"

  include_in_scope:
    - "Wrapper file (.md) - o arquivo principal do clone"
    - "Persona delegada - SE wrapper tem '@persona-file' ou 'persona:' -> incluir arquivo referenciado"
    - "Data files - SE wrapper referencia 'data/*.yaml' -> incluir no escopo"
    - "Heuristics files - SE wrapper referencia 'heuristics/*.yaml' -> incluir"

  explicit_rules:
    delegation_rule: |
      SE wrapper contem pattern '@{filename}' ou 'Read {path}'
      ENTAO incluir {filename}/{path} no escopo de avaliacao

    persona_rule: |
      SE wrapper delega para persona (ex: "You are @gary-halbert")
      ENTAO avaliar Trinity no arquivo da PERSONA, nao so no wrapper

    combined_rule: |
      Trinity score = checkpoints no WRAPPER + checkpoints em DELEGATED FILES
      Nao penalizar wrapper vazio se persona delegada tem conteudo

  anti_patterns:
    - "NAO avaliar so o wrapper se ele delega para persona"
    - "NAO ignorar conteudo em arquivos referenciados"
    - "NAO dar score 0 para swipe_file se exemplos estao na persona"
```

---

## MANDATORY PREFLIGHT: Run Worker Script FIRST

```
EXECUTE FIRST -- before ANY manual analysis:

  bash squads/squad-creator-pro/scripts/clone-review.sh <clone-file.md> [sources-dir] > /tmp/preflight-clone-review.yaml

IF the command fails -> FIX the script error. Do NOT proceed manually.
IF the command succeeds -> READ /tmp/preflight-clone-review.yaml. Use ONLY these numbers.

VETO: If /tmp/preflight-clone-review.yaml does not exist -> BLOCK.
```

---

## SCORING CALIBRATION (CRITICAL)

```yaml
scoring_philosophy:
  principle: "SCORE O QUE EXISTE, nao o que falta"
  bias_correction: "Haiku tende a sub-pontuar. Compensar sendo generoso."
  evidence_rule: "Se existe evidencia, conta ponto. Gaps vao para recommendations."
```

---

## Sub-Tasks (Atomic Execution)

| # | Sub-Task | File | Responsibility |
|---|----------|------|----------------|
| 1 | Source Quality + Trinity | `an-clone-review-source-trinity.md` | Source checkpoints (5 per source) + Trinity verification (15 checkpoints) |
| 2 | Stages + Fidelity | `an-clone-review-stages-fidelity.md` | Stage architecture review (5 checkpoints) + Quick fidelity check (5 checkpoints) |
| 3 | Report | `an-clone-review-report.md` | Generate consolidated review report with verdicts and priority actions |

---

## Execution Flow

```
Step 1: an-clone-review-source-trinity
  Input: clone file + preflight YAML
  Output: source_quality scores + trinity scores (playbook, framework, swipe_file)

Step 2: an-clone-review-stages-fidelity
  Input: clone file + preflight YAML
  Output: stage_score + quick_fidelity score

Step 3: an-clone-review-report
  Input: all scores from steps 1-2
  Output: clone_review YAML report with verdict, gaps, priority_actions
```

---

## Completion Criteria

- [ ] Fontes avaliadas com checkpoints binarios
- [ ] Trindade verificada (15 checkpoints total)
- [ ] Estagios revisados com checkpoints
- [ ] Quick fidelity com 5 checkpoints
- [ ] Report com percentages e gaps especificos

---

_Task Version: 2.0.0_
_Atomized: 2026-03-26_
_Sub-tasks: an-clone-review-source-trinity, an-clone-review-stages-fidelity, an-clone-review-report_

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Task-specific context and prior pipeline outputs
- **Outputs:** Completed an-clone-review output artifact
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] Fontes avaliadas com checkpoints binarios
- [ ] Trindade verificada (15 checkpoints total)
- [ ] Estagios revisados com checkpoints
- [ ] Quick fidelity com 5 checkpoints
- [ ] Report com percentages e gaps especificos
