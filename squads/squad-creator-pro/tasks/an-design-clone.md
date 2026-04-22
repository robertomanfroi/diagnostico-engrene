<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-design-clone
  task_name: Design Clone Architecture
  status: pending
  responsible_executor: Agent
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Define Contexts
  - Decide Stages
  - Map Trinity per Stage
  - Define Memory & Context
  - Generate Blueprint
  acceptance_criteria:
  - Contextos de uso mapeados
  - Decisao single vs multi-stage tomada
  - Trindade mapeada por estagio
  - Memoria/contexto definido
  - Blueprint YAML gerado
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


# Task: Design Clone Architecture

**Task ID:** an-design-clone  
**Version:** 3.1.0  
**Purpose:** compor o design de clone em fases atômicas de contexto, estágios, trindade, memória e blueprint

## Canonical Workflow

- `squads/squad-creator-pro/workflows/wf-design-clone.yaml`

## Atomic Sub-Tasks

- `an-design-clone-contexts.md`
- `an-design-clone-stages.md`
- `an-design-clone-trinity.md`
- `an-design-clone-memory.md`
- `an-design-clone-blueprint.md`

## Inputs

- `mind` e objetivo do clone são obrigatórios
- contextos de uso e perfis de usuário alimentam a arquitetura
- a geração do blueprint depende de stages, trinity e memory model completos

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-design-clone.yaml` existe
- [ ] as 5 subtasks atômicas existem
- [ ] o design multi-stage só fecha se cada estágio tiver playbook, framework e swipe file

## Execution Sequence

```text
[1] an-design-clone-contexts
[2] an-design-clone-stages
[3] an-design-clone-trinity
[4] an-design-clone-memory
[5] an-design-clone-blueprint
OUTPUT: clone_blueprint + estimated_fidelity
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-design-clone.yaml"
  context_map: {}
  stage_plan: {}
  clone_trinity: []
  memory_model: {}
  clone_blueprint: {}
```

## Acceptance Criteria

- [ ] contextos de uso são explicitados
- [ ] decisão single vs multi-stage fica justificada
- [ ] trindade por estágio é documentada
- [ ] memory model é definido com limites claros
- [ ] o wrapper não reimplementa localmente as 5 fases
