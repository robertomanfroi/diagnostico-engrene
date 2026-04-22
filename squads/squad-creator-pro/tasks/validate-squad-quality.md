<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad-quality
  task_name: Validate Squad - Quality
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
  - Prompt quality
  - Pipeline coherence
  - Checklist actionability
  - Documentation e optimization
  acceptance_criteria:
  - O output produz score e breakdown por dimensao
  - A amostragem e documentada no resultado
  - Findings sao classificados por severidade
  - O resultado pode ser combinado com a validacao contextual e com os vetos
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


# Task: Validate Squad - Quality

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-quality` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: validate-squad-quality
name: "Validate Squad Quality"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Avalia qualidade de prompts, coerencia operacional, actionability de checklists, documentacao e oportunidades de otimizacao."
```

## Purpose

Executar a camada semantica da validacao. Esta task so deve rodar depois dos gates deterministas, porque ela depende de amostragem e julgamento estruturado.

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
  squad_path:
    type: string
    required: false
    default: "squads/{squad_name}/"
  mode:
    type: string
    required: false
    default: "deep"
```

## Workflow / Steps

### Step 1: Prompt quality

- Amostrar tasks representativas.
- Pontuar clareza, exemplos, anti-patterns e criterios de sucesso.

### Step 2: Pipeline coherence

- Verificar cadeia output->input, checkpoints, dependencias e tratamento de falhas.

### Step 3: Checklist actionability

- Verificar se os itens sao mediveis, acionaveis e com thresholds claros.

### Step 4: Documentation e optimization

- Medir onboarding, exemplos, erros comuns, arquitetura e possiveis ganhos com melhor executor.

## Output

```yaml
output:
  schema:
    score: 0.0
    breakdown:
      prompt_quality: 0.0
      pipeline_coherence: 0.0
      checklist_actionability: 0.0
      documentation: 0.0
      optimization_opportunities: 0.0
    findings:
      critical: []
      high: []
      medium: []
```

## Acceptance Criteria

- [ ] O output produz score e breakdown por dimensao
- [ ] A amostragem e documentada no resultado
- [ ] Findings sao classificados por severidade
- [ ] O resultado pode ser combinado com a validacao contextual e com os vetos

## Related Documents

- `validate-squad.md`
- `validate-squad-contextual.md`
- `data/quality-dimensions-framework.md`
