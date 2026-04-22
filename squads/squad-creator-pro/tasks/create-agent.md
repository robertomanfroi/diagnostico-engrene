<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-agent
  task_name: Create Squad Agent (Extension Wrapper)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  action_items:
    - Normalize Target Squad
    - Reconcile Agent Source
    - Delegate to Canonical Pro Workflow
    - Reconcile Outputs for Pro Callers
  acceptance_criteria:
    - "workflows/wf-research-then-create-agent.yaml existe"
    - "pack_name e squad_name são reconciliados corretamente"
    - "o wrapper não mantém pipeline monolítico próprio"
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

# Task: Create Squad Agent (Extension Wrapper)

**Task ID:** create-agent  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` roteando a criação research-first de agentes para o workflow canônico do pack

## Canonical Owner

- `workflows/wf-research-then-create-agent.yaml`
- `workflows/wf-clone-mind.yaml` e `workflows/wf-mind-research-loop.yaml` como upstreams possíveis
- `tasks/create-task.md` como downstream para geração de tasks do agente

## Inputs

- `agent_purpose` e `domain` são obrigatórios
- `squad_name` é preferido; `pack_name` é alias legado
- `mind_slug`, `dna_bundle_path`, `specialist_slug`, `specialist_name` e `research_artifacts` qualificam a origem do agente

## Preconditions

- [ ] `workflows/wf-research-then-create-agent.yaml` existe
- [ ] o alvo resolve para `squads/{squad_name}/`
- [ ] o chamador entende que este arquivo não possui pipeline monolítico próprio

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

reconcile_source:
  rules:
    - if: "mind_slug ou dna_bundle_path presentes"
      then: "agent_source = dna-backed"
    - if: "specialist_slug ou specialist_name presentes"
      then: "agent_source = specialist-research"
    - else: "agent_source = domain-research"

delegate_to_pro_workflow:
  workflow: "workflows/wf-research-then-create-agent.yaml"
  contract:
    - use_pro_research_loop
    - reuse_clone_mind_outputs_if_present
    - preserve_research_artifacts_traceability
    - use_create_task_wrapper_for_downstream_generation
  prohibition:
    - "Do NOT recreate research phases here"
    - "Do NOT fork agent-definition logic locally"

reconcile_outputs:
  agent_file: "squads/{squad_name}/agents/{agent_id}.md"
  delegated_workflow: "workflows/wf-research-then-create-agent.yaml"
  execution_mode: "pro-delegated"
```

## Output

```yaml
output:
  agent_file: "squads/{squad_name}/agents/{agent_id}.md"
  delegated_workflow: "workflows/wf-research-then-create-agent.yaml"
  normalized_squad_name: "{squad_name}"
  agent_source: "dna-backed | specialist-research | domain-research"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] a criação real do agente é roteada para `wf-research-then-create-agent.yaml`
- [ ] DNA, research e handoffs upstream seguem preservados
- [ ] não existe segunda implementação monolítica de `create-agent` no pack

## Veto Conditions

- o pack tenta reimplementar localmente research, extraction ou quality gate
- `squad_name` e `pack_name` apontam para squads diferentes
- `wf-research-then-create-agent.yaml` não existe
