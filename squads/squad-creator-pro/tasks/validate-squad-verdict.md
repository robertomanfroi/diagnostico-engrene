<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad-verdict
  task_name: Validate Squad - Verdict
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Worker
  estimated_time: 15m
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Avaliar veto gates
  - Calcular score final
  - Gerar relatorios
  acceptance_criteria:
  - Vetos universais rodam antes dos vetos por tipo
  - O primeiro veto encontrado encerra com FAIL
  - O score final e consistente com qualidade, contextual e vetos
  - O report humano e o payload estruturado sao emitidos
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


# Task: Validate Squad - Verdict

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-verdict` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: validate-squad-verdict
name: "Validate Squad Verdict"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Consolida veto gates e geracao de relatorio final em uma unica task Worker. Avalia regras nao negociaveis e emite score + reports."
consolidates:
  - validate-squad-veto
  - validate-squad-report
```

## Purpose

Transformar regras nao negociaveis em decisao binaria, calcular o score final e emitir os relatorios consumiveis por humano e maquina. Score alto nao compensa falha estrutural. Preserva compatibilidade retroativa do comando `*validate-squad`.

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
  detected_type:
    type: string
    required: true
  structure_result:
    type: object
    required: true
  security_result:
    type: object
    required: true
  coverage_result:
    type: object
    required: true
  cross_reference_result:
    type: object
    required: true
  quality_result:
    type: object
    required: true
  contextual_result:
    type: object
    required: true
```

## Workflow / Steps

### Step 1: Evaluate Veto Gates

#### 1.1 Vetos universais

- Entry point ausente ou inativavel.
- Config invalido.
- Segredos expostos.
- Referencias criticas quebradas.

#### 1.2 Vetos por tipo

- `expert`: ausencia total de `voice_dna` ou capacidade de diagnostico.
- `pipeline`: fluxo sem gate final ou cadeia quebrada de outputs.
- `hybrid`: ausencia de heuristicas/fallback.

**Rule:** Vetos universais rodam antes dos vetos por tipo. O primeiro veto encontrado encerra a avaliacao.

### Step 2: Calculate Final Score

- Se houver veto, resultado final = `FAIL`.
- Sem veto, aplicar peso principal em qualidade e peso secundario em contextual.

### Step 3: Generate Reports

#### 3.1 Montar payload estruturado

- `final_score`
- `result`
- `veto_status`
- `tier_results`
- `issues_by_priority`
- `recommendations`

#### 3.2 Emitir relatorio humano

- Escrever `validation-report-{date}.md` em `docs/`.
- Escrever payload `.json` equivalente para automacao.

## Output

```yaml
output:
  schema:
    veto_status:
      status: "PROCEED | VETO"
      triggered_veto: null
      veto_message: null
      family: "universal | expert | pipeline | hybrid"
    final_score: 0.0
    result: "PASS | CONDITIONAL | FAIL"
    detected_type: "expert | pipeline | hybrid"
  files:
    report: "{squad_path}/docs/validation-report-{date}.md"
    json: "{squad_path}/docs/validation-report-{date}.json"
```

## Acceptance Criteria

- [ ] Vetos universais rodam antes dos vetos por tipo
- [ ] O primeiro veto encontrado encerra a task
- [ ] O motivo do veto fica claro e acionavel
- [ ] O score final e consistente com qualidade, contextual e vetos
- [ ] O report humano e o payload estruturado sao emitidos
- [ ] O formato final continua compativel com o uso atual do comando

## Related Documents

- `validate-squad.md`
- `validate-squad-deterministic.md`
- `validate-squad-quality.md`
- `validate-squad-contextual.md`
