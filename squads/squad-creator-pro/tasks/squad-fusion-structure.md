<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-structure
  task_name: Squad Fusion - Structure
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 30m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Coletar componentes aprovados para workspace
  - Materializar estrutura final do target
  acceptance_criteria:
  - So componentes aprovados entram no workspace [threshold: >= 1]
  - Todo conflito resolvido fica registrado [threshold: >= 1]
  - A provenance do merge fica preservada [threshold: >= 1]
  - O target final e criado de forma deterministica [threshold: >= 1]
  - Config e contagens finais fecham com o workspace validado [threshold: score >= 0.8]
  - Metadados de fusao permanecem acessiveis [threshold: >= 1]
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


# Task: Squad Fusion - Structure

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-structure` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |
| **Merges** | `squad-fusion-collection` + `squad-fusion-structure` |

## Metadata

```yaml
id: squad-fusion-structure
name: "Squad Fusion Structure"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Executa o ETL extract+load: coleta componentes selecionados para o workspace com provenance e materializa a estrutura final do squad fusionado."
```

## Purpose

Montar o workspace de fusao copiando componentes aprovados com rastreabilidade completa, e em seguida transformar o workspace temporario validado na estrutura final do squad fusionado.

## Workflow / Steps

### Step 1: Coletar componentes para workspace

Executar o ETL extract: copiar componentes selecionados para o workspace temporario e registrar provenance.

- Copiar assets de `final_components` para o workspace.
- Resolver conflitos fisicos de nome e path.
- Produzir `workspace_contents`, `conflicts_resolved` e `provenance_map`.
- Garantir que cada asset do workspace aponte para sua origem.

### Step 2: Materializar estrutura final do target

Transformar o workspace temporario validado na estrutura final do squad fusionado.

- Materializar `squads/{target_name}/`.
- Escrever config, assets fusionados e arquivos obrigatorios.
- Registrar `final_counts`, `config_valid` e metadados de fusao.
- Garantir que README e artefatos de auditoria reflitam a fusao.

## Output

```yaml
# Collection output
collection:
  workspace_contents: []
  conflicts_resolved: []
  provenance_map: {}

# Structure output
structure:
  squad_path: string
  config_valid: true
  final_counts: {}
```

## Acceptance Criteria

- [ ] So componentes aprovados entram no workspace [threshold: >= 1]
- [ ] Todo conflito resolvido fica registrado [threshold: >= 1]
- [ ] A provenance do merge fica preservada [threshold: >= 1]
- [ ] O target final e criado de forma deterministica [threshold: >= 1]
- [ ] Config e contagens finais fecham com o workspace validado [threshold: score >= 0.8]
- [ ] Metadados de fusao permanecem acessiveis [threshold: >= 1]

## Related Documents

- `squad-fusion.md` -- Parent stub task
- `squad-fusion-scope.md` -- Previous phase
- `squad-fusion-resolution.md` -- Previous phase (resolution feeds structure)
- `squad-fusion-validation.md` -- Validates before final write

_Task Version: 2.0.0 -- Merged from squad-fusion-collection + squad-fusion-structure_
