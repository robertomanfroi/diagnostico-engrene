<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-initialize
  task_name: Squad Fusion - Initialize
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Hybrid
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Elicitar parametros de fusao
  - Validar entrada e criar workspace
  acceptance_criteria:
  - All 5 elicitation steps presented in sequence [threshold: >= 5]
  - 'Validation enforced: minimum 2 sources, kebab-case target name [threshold: >= 2]'
  - CLI argument bypass works when `--sources` and `--target` provided [threshold: >= 1]
  - Confirmation summary accurately reflects collected inputs [threshold: >= 1]
  - Cancel option aborts without side effects [threshold: >= 1]
  - Pelo menos duas fontes validas foram confirmadas [threshold: >= 2]
  - Workspace, backup e audit log foram definidos [threshold: >= 3]
  - O processo bloqueia cedo quando houver input invalido [threshold: >= 1]
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Squad Fusion - Initialize

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-initialize` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |
| **Merges** | `squad-fusion-elicitation` + `squad-fusion-initialize` |

## Metadata

```yaml
id: squad-fusion-initialize
name: "Squad Fusion Initialize"
category: fusion
agent: squad-chief
elicit: true
autonomous: false
description: "Coleta inputs do usuario para configurar a fusao e prepara o ambiente controlado: fontes validas, target resolvido, rollback preparado e trilha de auditoria aberta."
```

## Purpose

Setup completo da fusao em duas etapas: primeiro coleta os parametros do usuario (squads fonte, target, escopo, modo e confirmacao), depois valida as entradas e cria o workspace de execucao com backup e audit log.

## Workflow / Steps

### Step 1: Elicitar parametros de fusao

Coletar todos os inputs necessarios para configurar a operacao de Squad Fusion. Cinco sub-steps sequenciais:

#### 1.1: Identificar Squads Fonte

```yaml
elicit:
  id: step_1_sources
  question: "Quais squads deseja fundir?"
  type: multi_select
  options:
    source: "Listar squads disponiveis em squads/"
    display: "nome (agents: N, tasks: N)"
  validation:
    min: 2
    max: 10
    error_if_less: "Fusao requer pelo menos 2 squads"
  hints:
    - "Selecione squads com dominios similares para melhor resultado"
    - "Squads muito diferentes podem resultar em fusao inconsistente"
```

#### 1.2: Definir Target

```yaml
elicit:
  id: step_2_target
  question: "Nome do squad resultante?"
  type: text
  default: "Sugerir baseado nos fontes (ex: traffic-masters)"
  validation:
    pattern: "^[a-z][a-z0-9-]*$"
    error: "Nome deve ser kebab-case"
  auto_suggest:
    - Analisar nomes dos fontes
    - Identificar dominio comum
    - Propor nome que representa uniao
```

#### 1.3: Definir Escopo

```yaml
elicit:
  id: step_3_scope
  question: "Qual o escopo/dominio do squad fusionado?"
  type: select
  options:
    - label: "Full Merge - Manter todos os componentes"
      value: full
      description: "Combina tudo, ideal para squads complementares"
    - label: "Domain Filter - Filtrar por keywords"
      value: filtered
      description: "Apenas componentes que matcham keywords"
    - label: "Cherry Pick - Selecionar manualmente"
      value: manual
      description: "Voce escolhe cada componente"
  follow_up:
    if: filtered
    then:
      question: "Quais keywords definir o escopo?"
      type: text_array
      example: ["paid traffic", "meta ads", "google ads"]
```

#### 1.4: Definir Modo de Execucao

```yaml
elicit:
  id: step_4_mode
  question: "Modo de execucao?"
  type: select
  options:
    - label: "YOLO (automatico, ~15-30 min)"
      value: yolo
      description: |
        - Decisoes automaticas para conflitos
        - Prefer newer version em duplicatas
        - Merge automatico de configs
        - Checkpoint apenas no final
    - label: "QUALITY (checkpoints, ~45-90 min)"
      value: quality
      description: |
        - Checkpoint em cada fase
        - Revisao humana de conflitos
        - Validacao manual de deduplicacao
        - Quality gate rigoroso
```

#### 1.5: Confirmar Configuracao

```yaml
elicit:
  id: step_5_confirm
  question: "Confirmar configuracao?"
  type: confirm
  display: |
    RESUMO DA FUSAO

    Squads Fonte: {sources.join(', ')}
    Target: {target_name}
    Escopo: {scope}
    Modo: {mode}

    Componentes a fundir:
    - Agents: {total_agents} -> ~{estimated_agents}
    - Tasks: {total_tasks} -> ~{estimated_tasks}
    - Workflows: {total_workflows} -> ~{estimated_workflows}
  options:
    - "Confirmar e executar"
    - "Modificar configuracao"
    - "Cancelar"
```

### Step 2: Validar entrada e criar workspace

Garantir que a fusao comeca em ambiente controlado com rollback preparado.

- Confirmar `sources.length >= 2`.
- Confirmar que todos os squads fonte existem e sao legiveis.
- Validar `target_name` em kebab-case.
- Gerar `fusion_id`, `workspace_path`, `backup_path` e `audit_log_path`.
- Registrar parametros de execucao (`mode`, `dry_run`, `keep_sources`, `verbose`).

## Output

```yaml
# Elicitation output
fusion_config:
  sources: ["{squad-a}", "{squad-b}", ...]
  target_name: "{target-name}"
  scope: "full | filtered | manual"
  scope_keywords: ["..."]  # only if scope=filtered
  mode: "yolo | quality"
  confirmed: true

# Initialization output
fusion_runtime:
  fusion_id: string
  workspace_path: string
  backup_path: string
  audit_log_path: string
  inputs_valid: true
```

## Acceptance Criteria

- [ ] All 5 elicitation steps presented in sequence [threshold: >= 5]
- [ ] Validation enforced: minimum 2 sources, kebab-case target name [threshold: >= 2]
- [ ] CLI argument bypass works when `--sources` and `--target` provided [threshold: >= 1]
- [ ] Confirmation summary accurately reflects collected inputs [threshold: >= 1]
- [ ] Cancel option aborts without side effects [threshold: >= 1]
- [ ] Pelo menos duas fontes validas foram confirmadas [threshold: >= 2]
- [ ] Workspace, backup e audit log foram definidos [threshold: >= 3]
- [ ] O processo bloqueia cedo quando houver input invalido [threshold: >= 1]

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-SFU-001 | Fewer than 2 valid source squads selected | BLOCK. Provide at least two valid source squads. |

## Related Documents

- `squad-fusion.md` -- Parent stub task
- `squad-fusion-discovery.md` -- Next phase (Phase 2)

_Task Version: 2.0.0 -- Merged from squad-fusion-elicitation + squad-fusion-initialize_
