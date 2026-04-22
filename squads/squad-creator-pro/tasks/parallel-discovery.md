<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: parallel-discovery
  task_name: Parallel Discovery
  status: pending
  responsible_executor: '@squad-chief'
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
  - 'Output artifact produced: Completed parallel-discovery output artifact'
  - Task output validated against quality standards
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Parallel Discovery

**Task ID:** parallel-discovery
**Execution Type:** Hybrid (Worker parallelization + Agent synthesis)
**Model:** Sonnet
**Haiku Eligible:** NO
**Purpose:** Run domain discovery streams in parallel and merge deterministically
**Orchestrator:** @squad-chief

## Parallel Streams

```yaml
streams:
  market_signals:
    source: web + docs
    output: market-signals.yaml

  expert_minds:
    source: mind research
    output: expert-candidates.yaml

  tooling_stack:
    source: tool registry + MCP discovery
    output: tooling-options.yaml

  risk_constraints:
    source: architecture and governance docs
    output: risks-and-vetos.yaml
```

---

## Merge Strategy

1. Normalize outputs to YAML schema.
2. Deduplicate by key and source confidence.
3. Resolve conflicts using priority: `local > primary source > secondary source`.
4. Emit `discovery-merged.yaml` and `discovery-summary.md`.

---

## Output

```yaml
discovery_bundle:
  merged_file: .aiox/squad-runtime/discovery/{domain}/discovery-merged.yaml
  summary_file: .aiox/squad-runtime/discovery/{domain}/discovery-summary.md
  confidence_score: 0-1
  unresolved_conflicts:
    - "..."
```

---

## Success Criteria

- At least 3 streams completed successfully.
- Merged output has explicit source attribution.
- No unresolved critical conflicts.

## Task Anatomy

- **Executor:** Worker
- **Inputs:** Pipeline context from prior tasks
- **Outputs:** Completed parallel-discovery output artifact
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] Output artifact produced: Completed parallel-discovery output artifact
- [ ] Task output validated against quality standards
