<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-scope
  task_name: Squad Fusion - Scope
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
  - Aplicar política de escopo
  - Fechar lista final
  acceptance_criteria:
  - O escopo aplicado é rastreável [threshold: >= 1]
  - Os componentes finais são coerentes com o target [threshold: score >= 0.8]
  - As exclusões têm motivo explícito [threshold: >= 1]
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


# Task: Squad Fusion - Scope

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-scope` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: squad-fusion-scope
name: "Squad Fusion Scope"
category: fusion
agent: squad-chief
elicit: false
autonomous: true
description: "Aplica o escopo escolhido para manter apenas componentes coerentes com o domínio do squad fusionado."
```

## Purpose

Filtrar componentes fora do domínio ou desalinhados com o target, evitando um squad fusionado inflado e incoerente.

## Workflow / Steps

### Step 1: Aplicar política de escopo

- Interpretar `scope` como `full`, `filtered` ou `manual`.
- Quando houver keywords, usar correspondência semântica e estrutural.

### Step 2: Fechar lista final

- Produzir `final_components` e `excluded_components`.
- Justificar exclusões com base em escopo, não em preferência subjetiva.

## Output

```yaml
output:
  schema:
    final_components: []
    excluded_components: []
```

## Acceptance Criteria

- [ ] O escopo aplicado é rastreável [threshold: >= 1]
- [ ] Os componentes finais são coerentes com o target [threshold: score >= 0.8]
- [ ] As exclusões têm motivo explícito [threshold: >= 1]
