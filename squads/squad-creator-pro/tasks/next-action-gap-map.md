<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: next-action-gap-map
  task_name: Next Action -- Gap Map
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Agent
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Map Blocking Signals
  - Map Non-Blocking Signals
  - Define Ready-State Default
  acceptance_criteria:
  - All blocking signals mapped with detection + next_action
  - All non-blocking signals mapped with detection + next_action
  - Ready-state default defined
  - Priority order enforced (blocking > non_blocking > ready_state)
  - No CTA uses generic commands when blocker exists
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


# Task: Next Action -- Gap Map

**Task ID:** next-action-gap-map
**Parent Task:** `next-action.md`
**Purpose:** Build decision table mapping observed signals to prioritized next actions
**Orchestrator:** @squad-chief
**Execution Type:** `Agent`
**Model:** `Opus`
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Next Action -- Gap Map |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `next_action_discovery` YAML from `next-action-discovery.md` |
| **output** | `gap_map` YAML with signal-to-action mappings |
| **action_items** | 3 steps |
| **acceptance_criteria** | All signals mapped, blocking gaps prioritized, no inference-based CTAs |

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-NA-003 | CTA final contradiz gap bloqueante explicito | Se houver blocker/readiness `not_ready`/`missing_*`, Next Action deve priorizar remediacao, nao intake generico | VETO - BLOCK. Corrigir a prioridade da heuristica. |

---

## Heuristica Obrigatoria

O proximo passo deve ser inferido por prioridade:

### Prioridade 1: Gap bloqueante

Exemplos:

- `campaign-brief.yaml` ausente -> `*create-campaign-brief ...`
- DS context nao inicializado -> `set-active-context`
- readiness nao resolvido -> `*show-context` ou comando de preflight
- credenciais ausentes -> `*setup-credentials`

### Prioridade 2: Gap estrutural nao-bloqueante

Exemplos:

- contexto incompleto mas utilizavel -> `*show-context`
- blueprint/token faltando -> `*review-plan ...`
- rota ainda ambigua -> `*resolve-ds ...`

### Prioridade 3: Intake operacional

Se nao houver gap relevante:

- usar intake/triage/briefing como proximo passo
- exemplo: `*triage {request}`

### Regra dura

Se existir blocker explicito, **nunca** usar CTA generico como `*triage`, `*diagnose`, `*route` antes de oferecer a remediacao do blocker.

---

## Workflow

### Step 1: Map Blocking Signals

For each context source from discovery, identify blocking conditions:

```yaml
blocking_signals:
  - signal: "missing_campaign_brief"
    detection: "file does not exist at expected path"
    next_action: "*create-campaign-brief --business={business} --product={product}"
  - signal: "no_active_context"
    detection: "session-context.yaml missing or empty"
    next_action: "node squads/{squad}/scripts/set-active-context.cjs ..."
```

### Step 2: Map Non-Blocking Signals

```yaml
non_blocking_signals:
  - signal: "context_incomplete"
    detection: "session-context exists but missing optional fields"
    next_action: "*show-context"
  - signal: "blueprint_missing"
    detection: "no blueprint file in runtime"
    next_action: "*review-plan ..."
```

### Step 3: Define Ready-State Default

```yaml
ready_state:
  signal: "context_ready"
  detection: "all blocking signals clear, context loaded"
  next_action: "*triage {request}"
```

Rules:

- Map only signals observable in code/runtime
- Avoid heuristics dependent on LLM session memory
- Prefer commands already existing in the squad

---

## Output Contract

```yaml
gap_map:
  squad_name: "{squad_name}"
  blocking:
    - signal: "{signal_id}"
      severity: "blocking"
      detection: "{how to detect}"
      next_action: "{command}"
  non_blocking:
    - signal: "{signal_id}"
      severity: "non_blocking"
      detection: "{how to detect}"
      next_action: "{command}"
  ready_state:
    signal: "context_ready"
    next_action: "{default intake command}"
  priority_order: "blocking > non_blocking > ready_state"
```

---

## Contrato Minimo do Padrao

O squad alvo deve implement, no minimo:

1. Uma funcao explicita de inferencia: `inferNextAction(context)`
2. Um construtor de callout: `buildNextActionCallout(context)`
3. Insercao do callout no **fim** do greeting
4. Teste cobrindo: bootstrap sem contexto, contexto pronto sem blocker, contexto com blocker/gap explicito

---

## Completion Criteria

- [ ] All blocking signals mapped with detection + next_action
- [ ] All non-blocking signals mapped with detection + next_action
- [ ] Ready-state default defined
- [ ] Priority order enforced (blocking > non_blocking > ready_state)
- [ ] No CTA uses generic commands when blocker exists

---

## Handoff

| Attribute | Value |
|-----------|-------|
| **Next Task** | `next-action-implement.md` |
| **Trigger** | Gap map complete |
| **Artifact** | `gap_map` YAML |

---

_Task Version: 1.0.0_
_Pattern: Atomic sub-task of next-action.md_

## Acceptance Criteria

- [ ] All signals mapped
- [ ] blocking gaps prioritized
- [ ] no inference-based CTAs
