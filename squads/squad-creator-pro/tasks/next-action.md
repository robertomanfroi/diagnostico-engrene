<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: next-action
  task_name: Next Action (Stub)
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
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Squad alvo possui `Next Action` final no greeting
  - O `Next Action` e inferido de gaps/contexto atuais, nao apenas do runtime ativo
  - Gaps bloqueantes sao priorizados sobre comandos genericos
  - O callout final usa o formato `**Next Action:** \`...\
  - Existe teste automatizado cobrindo os cenarios principais
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


# Task: Next Action (Stub)

**Task ID:** next-action
**Purpose:** Padronizar greetings stateful com `Next Action` final, inferido de gaps atuais e continuidade operacional
**Orchestrator:** @squad-chief
**Mode:** Audit + Implementation
**Pattern:** GREETING-CONTINUITY-001
**Execution Type:** `Agent` (exige leitura estrutural de runtime, greeting e contratos de contexto)
**Model:** `Opus` (REQUIRED -- erro de heuristica no proximo passo degrada UX operacional)
**Haiku Eligible:** NO

---

## Task Anatomy

| Field | Value |
|-------|-------|
| **task_name** | Next Action |
| **status** | `active` |
| **responsible_executor** | @squad-chief |
| **execution_type** | Agent |
| **input** | `squad_name` ou `greeting_script_path` |
| **output** | Greeting atualizado + heuristica de `Next Action` + teste unitario |
| **action_items** | 3 sub-tasks |
| **acceptance_criteria** | Greeting termina com `**Next Action:** \`...\`` coerente com gaps/continuidade |

---

## Command

```text
*next-action {squad_name}
```

Flags:

- `--audit` (default): diagnosticar sem editar
- `--apply`: implementar o padrao no squad alvo
- `--strict`: bloquear se nao houver teste automatizado do greeting
- `--report {path}`: salvar relatorio explicito

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-NA-001 | Squad sem greeting custom | Verificar se existe `generate-*-greeting.*` ou equivalente | VETO - BLOCK |
| VETO-NA-002 | Heuristica sem fonte estrutural de contexto | Verificar se squad possui `load-context`, `runtime-paths`, `session-context` ou equivalentes | VETO - BLOCK |
| VETO-NA-003 | CTA final contradiz gap bloqueante explicito | Se houver blocker/readiness `not_ready`/`missing_*`, Next Action deve priorizar remediacao | VETO - BLOCK |
| VETO-NA-004 | Greeting alterado sem teste minimo | Verificar teste unitario ou de contrato cobrindo o CTA final | VETO - BLOCK |

---

## Sub-Tasks (Atomic Execution)

| # | Sub-Task | File | Responsibility |
|---|----------|------|----------------|
| 1 | Discovery | `next-action-discovery.md` | Map greeting scripts, context loaders, runtime files, and existing gaps |
| 2 | Gap Map | `next-action-gap-map.md` | Build decision table mapping signals to next actions by priority |
| 3 | Implement | `next-action-implement.md` | Apply pattern to greeting script, add CTA, create validation tests |

---

## Execution Flow

```
Step 1: next-action-discovery
  Input: squad_name
  Output: discovery map (greeting_script, context_sources, existing_commands, user_friction_points)

Step 2: next-action-gap-map
  Input: discovery map
  Output: gap_map with blocking/non-blocking/ready signals and mapped next_actions

Step 3: next-action-implement (only with --apply)
  Input: gap_map + greeting_script
  Output: updated greeting with CTA + validation tests
```

---

## Acceptance Criteria

- [ ] Squad alvo possui `Next Action` final no greeting
- [ ] O `Next Action` e inferido de gaps/contexto atuais, nao apenas do runtime ativo
- [ ] Gaps bloqueantes sao priorizados sobre comandos genericos
- [ ] O callout final usa o formato `**Next Action:** \`...\``
- [ ] Existe teste automatizado cobrindo os cenarios principais

---

## Recommended Rollout Order

1. `copy`
2. `design`
3. `traffic-masters`
4. `application-forms`
5. `storytelling`
6. `hormozi`
7. `movement`

---

_Task Version: 2.0.0_
_Atomized: 2026-03-26_
_Sub-tasks: next-action-discovery, next-action-gap-map, next-action-implement_
