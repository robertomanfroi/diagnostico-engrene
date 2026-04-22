<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: lookup-model
  task_name: lookup-model
  status: pending
  responsible_executor: Worker
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Load Config
  - Lookup Task
  - Return Result
  acceptance_criteria:
  - Task name provided
  - Config loaded
  - Tier returned
  - If task not found, return "opus" (safe default)
  - 'Output artifact produced: Completed lookup-model output artifact'
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
  Domain: Strategic
  atomic_layer: Atom
  executor: Worker
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: lookup-model

**Command:** `*lookup-model <task-name>`
**Execution Type:** Worker (deterministic, no LLM needed)
**Model:** Haiku
**Haiku Eligible:** YES

## Purpose

Look up the recommended model tier for a Squad Creator task before execution.
Returns: `haiku`, `sonnet`, or `opus`.

## Usage

```bash
# In Squad Chief or any workflow
model=$(lookup-model "create-agent.md")
# Returns: opus

model=$(lookup-model "validate-squad.md")
# Returns: haiku
```

## Workflow

### Step 1: Load Config

Read `config/model-routing.yaml`

### Step 2: Lookup Task

```yaml
task_name: "{input}"
config: model-routing.yaml

lookup:
  path: tasks.{task_name}.tier
  default: opus  # Conservative default
```

### Step 3: Return Result

```yaml
output:
  task: "{task_name}"
  tier: "{haiku|sonnet|opus}"
  confidence: "{high|medium|low}"
  reason: "{why this tier}"
```

## Quick Reference

| Tier | Tasks Count | Use For |
|------|-------------|---------|
| **haiku** | 13 | Validation, scoring, admin |
| **sonnet** | 17 | Documentation, templates, moderate analysis |
| **opus** | 12 | DNA extraction, agent creation, research |

## Integration with Task Tool

When spawning agents, use the tier as model parameter:

```python
# Pseudo-code for Squad Chief
task = "validate-squad.md"
tier = lookup_model(task)  # Returns "haiku"

Task(
  subagent_type="general-purpose",
  model=tier,  # "haiku"
  prompt="Execute validation..."
)
```

## Completion Criteria

- [ ] Task name provided
- [ ] Config loaded
- [ ] Tier returned
- [ ] If task not found, return "opus" (safe default)

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Task-specific context and prior pipeline outputs
- **Outputs:** Completed lookup-model output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** None identified

## Acceptance Criteria

- [ ] Output artifact produced: Completed lookup-model output artifact
- [ ] Task output validated against quality standards
