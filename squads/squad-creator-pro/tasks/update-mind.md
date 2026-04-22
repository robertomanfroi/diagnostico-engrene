---
task-id: update-mind
name: "Update Existing Agent DNA (Brownfield)"
version: 3.0.0
execution_type: Orchestrator
model: Sonnet
model_rationale: "Orchestrator stub -- delegates to 4 atomic sub-tasks. Sonnet for merge strategy decisions."
haiku_eligible: false
note: "Decomposed from v2.0.0 monolith (437 lines, 5 phases) into 4 atomic tasks."
estimated-time: 1-2 hours
complexity: medium

inputs:
  required:
    - squad_name: "Nome do squad (ex: copy, legal)"
    - agent_slug: "Slug do agent existente (snake_case)"
  optional:
    - new_sources_path: "Caminho para novas fontes"
    - focus: "voice|thinking|both (default: both)"
    - mode: "merge|replace|selective"

outputs:
  primary:
    - updated_agent: "Agent file atualizado com novo DNA"
    - diff_report: "Relatorio do que mudou"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: update-mind
  task_name: Update Existing Agent DNA (Brownfield)
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 1-2h
  domain: Operational
  input:
  - '{''squad_name'': ''Nome do squad (ex: copy, legal)''}'
  - '{''agent_slug'': ''Slug do agent existente (snake_case)''}'
  - '{''new_sources_path'': ''Caminho para novas fontes''}'
  - '{''focus'': ''voice|thinking|both (default: both)''}'
  - '{''mode'': ''merge|replace|selective''}'
  output:
  - '{''updated_agent'': ''Agent file atualizado com novo DNA''}'
  - '{''diff_report'': ''Relatorio do que mudou''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - DNA existente carregado com sucesso
  - Snapshot "before" criado
  - Novas fontes processadas
  - Conflicts identificados e resolvidos
  - Backup criado antes de modificar
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


# Update Existing Agent DNA (Brownfield)

> **Principio:** "Evolucao > Revolucao. Preserve o que funciona, adicione o que falta."
>
> **Regra:** NUNCA substituir DNA existente sem validar que o novo e melhor.

---

## Pipeline (4 Atomic Tasks)

| Phase | Task ID | Name | Est. Time |
|-------|---------|------|-----------|
| 1 | `update-mind-load` | Load Existing DNA & Snapshot | 5 min |
| 2 | `update-mind-extract` | Process & Extract from New Sources | 45 min |
| 3 | `update-mind-merge` | Merge Strategy & Conflict Resolution | 15 min |
| 4 | `update-mind-apply` | Apply Updates & Diff Report | 15 min |

---

## Execution Flow

```
update-mind-load
  | existing_dna, snapshot_before
  v
update-mind-extract
  | voice_delta, thinking_delta
  v
update-mind-merge
  | merge_plan, resolved_conflicts
  v
update-mind-apply
  | updated_agent, diff_report (FINAL OUTPUT)
  v
[DONE]
```

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-UPM-001 | Backup of current mind files must exist before any modification | Verify backup created at squads/{squad_name}/.backup/{agent_slug}.{timestamp}.md | VETO - BLOCK. Create backup snapshot before proceeding. |
| VETO-UPM-002 | Existing agent file must be loadable and parseable | Validate agent file exists and YAML blocks parse without error | VETO - BLOCK. Fix agent file path or structure first. |
| VETO-UPM-003 | Protected sections must not be replaced without human approval | Check merge_rules.protected list against proposed changes | VETO - BLOCK. Route through selective mode with human review. |

---

## Merge Modes

| Mode | Behavior |
|------|----------|
| **merge** | Add new elements, preserve existing |
| **replace** | Replace sections where new is significantly better |
| **selective** | Checkpoint per section, user decides |

---

## Commands

```bash
*update-mind copy gary_halbert --sources /path/to/new/materials
*update-mind copy gary_halbert --focus voice --sources /path/to/interviews
*update-mind legal contract_lawyer --mode selective
```

---

## Quality Check

- [ ] DNA existente carregado com sucesso
- [ ] Snapshot "before" criado
- [ ] Novas fontes processadas
- [ ] Conflicts identificados e resolvidos
- [ ] Backup criado antes de modificar
- [ ] Diff report gerado
- [ ] Quality scores atualizados

---

**Squad Architect | Update Agent DNA v3.0**
_Last Updated: 2026-03-26_
*"Evolution beats revolution. Preserve what works, add what's missing."*

## Task Anatomy

- **Executor:** Agent
- **Inputs:** squad_name; agent_slug
- **Outputs:** Agent file atualizado com novo DNA; Relatorio do que mudou
- **Completion Criteria:** All items in Quality Check/Completion Criteria above are satisfied
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] DNA existente carregado com sucesso
- [ ] Snapshot "before" criado
- [ ] Novas fontes processadas
- [ ] Conflicts identificados e resolvidos
- [ ] Backup criado antes de modificar
- [ ] Diff report gerado
- [ ] Quality scores atuali
