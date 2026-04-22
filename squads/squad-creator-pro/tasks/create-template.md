<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: create-template
  task_name: Create Squad Template (Extension Wrapper)
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Operational
  action_items:
    - Normalize Target Squad
    - Delegate to Base Task
    - Reconcile Outputs
  acceptance_criteria:
    - "squads/squad-creator/tasks/create-template.md existe"
    - "pack_name e squad_name são reconciliados corretamente"
    - "o wrapper não define pipeline próprio"
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

# Task: Create Squad Template (Extension Wrapper)

**Task ID:** create-template  
**Version:** 3.1.0  
**Purpose:** manter compatibilidade do `squad-creator-pro` delegando a criação real de templates ao owner canônico do base

## Canonical Owner

- `squads/squad-creator/tasks/create-template.md`
- `squads/squad-creator/workflows/wf-create-template.yaml`

## Inputs

- `template_name`, `template_id` e `output_format` são obrigatórios
- `squad_name` é preferido; `pack_name` é alias legado
- `source_artifacts` só enriquecem a delegação

## Preconditions

- [ ] `squads/squad-creator/tasks/create-template.md` existe
- [ ] o alvo resolve para `squads/{squad_name}/`
- [ ] o chamador entende que este wrapper não possui pipeline próprio

## Execution Contract

```yaml
normalize_target:
  rules:
    - if: "squad_name vazio e pack_name presente"
      then: "set squad_name = pack_name"
    - if: "squad_name e pack_name divergem"
      then: "block and reconcile"

delegate_to_base:
  task: "squads/squad-creator/tasks/create-template.md"
  payload:
    - template_name
    - template_id
    - squad_name
    - output_format
    - source_artifacts
  prohibition:
    - "Do NOT maintain a parallel template-creation methodology in squad-creator-pro"

reconcile_outputs:
  template_file: "squads/{squad_name}/templates/{template_id}-tmpl.{ext}"
  delegated_task: "squads/squad-creator/tasks/create-template.md"
  execution_mode: "base-delegated"
```

## Output

```yaml
output:
  template_file: "squads/{squad_name}/templates/{template_id}-tmpl.{ext}"
  delegated_task: "squads/squad-creator/tasks/create-template.md"
  normalized_squad_name: "{squad_name}"
  status: "delegated"
```

## Acceptance Criteria

- [ ] `pack_name` e `squad_name` são reconciliados corretamente
- [ ] a criação real do template é delegada ao base
- [ ] nenhuma implementação paralela de create-template permanece no pro
- [ ] chamadas existentes do pro continuam compatíveis
