<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: optimize-determinism-analysis
  task_name: Optimize - Determinism Analysis
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
  - Carregar dependências obrigatórias
  - Resolver o target
  - Inventariar artefatos e restrições
  - Decompor a task em ações
  - Aplicar Q1-Q6 por ação
  - Agregar por task
  acceptance_criteria:
  - O target é resolvido sem ambiguidade
  - O decision tree foi carregado antes de qualquer classificação
  - O inventário lista arquivos, escopo e pré-condições do modo
  - Nenhuma task é classificada só pelo filename
  - Cada ação recebe resposta explícita para Q1-Q6
  - O output identifica as melhores candidatas a Worker/Hybrid
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
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


# Task: Optimize - Determinism Analysis

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `optimize-determinism-analysis` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: optimize-determinism-analysis
name: "Optimize Determinism Analysis"
category: optimization
agent: squad-chief
elicit: false
autonomous: true
description: "Carrega o framework de decisao, resolve o target, produz o inventario factual e aplica o decision tree Q1-Q6 para recomendar Worker, Agent, Hybrid ou Human."
absorbs:
  - optimize-target-inventory
```

## Purpose

Resolver `target`, `mode` e `focus` em um inventário determinístico e, em seguida, executar a análise semântica Q1-Q6 sobre cada ação de cada task. Impede que a otimização comece por intuição ou por nome de arquivo e transforma o conteúdo real das tasks em uma análise tabular auditável.

## Inputs

```yaml
inputs:
  target:
    type: string
    required: true
  mode:
    type: string
    required: false
    default: scan
  focus:
    type: string
    required: false
    default: tasks
```

## Workflow / Steps

### Step 0: Target Inventory (absorbed from optimize-target-inventory)

#### Step 0.1: Carregar dependências obrigatórias

- Ler `squads/squad-creator/data/executor-decision-tree.md` por completo.
- Confirmar que o operador sabe aplicar Q1-Q6 literalmente.

#### Step 0.2: Resolver o target

- Se `target` for arquivo, operar em uma task específica.
- Se `target` for nome de squad, listar `tasks/*.md` do squad.
- Se `target = all`, listar tasks de todos os squads elegíveis e excluir o meta-squad.

#### Step 0.3: Inventariar artefatos e restrições

- Registrar arquivos alvo, tamanho, tipo e execution_type atual.
- Marcar se o modo exige backup prévio (`implement` ou `hybrid`).
- Emitir inventário reutilizável pelas phases seguintes.

### Step 1: Decompor a task em ações

- Ler cada task alvo por completo.
- Extrair cada ação executável como linha separada.

### Step 2: Aplicar Q1-Q6 por ação

- Responder o fluxo completo do decision tree para cada ação.
- Classificar cada linha como `Worker`, `Agent`, `Hybrid` ou `Human`.

### Step 3: Agregar por task

- Calcular distribuição por executor.
- Sugerir classificação final da task.
- Listar justificativa e risco de erro de classificação.

## Output

```yaml
output:
  schema:
    resolved_scope: "single-task | squad | all"
    target_files: []
    current_execution_types: []
    decision_tree_loaded: true
    backups_required: true
    analysis_table: []
    task_recommendations: []
    high_roi_targets: []
```

## Acceptance Criteria

- [ ] O target é resolvido sem ambiguidade
- [ ] O decision tree foi carregado antes de qualquer classificação
- [ ] O inventário lista arquivos, escopo e pré-condições do modo
- [ ] Nenhuma task é classificada só pelo filename
- [ ] Cada ação recebe resposta explícita para Q1-Q6
- [ ] O output identifica as melhores candidatas a Worker/Hybrid

## Related Documents

- `optimize.md`
- `optimize-scope-clarification.md`
- `squads/squad-creator/data/executor-decision-tree.md`

_Task Version: 2.0.0_
_Absorbs: optimize-target-inventory (v1.0.0)_
