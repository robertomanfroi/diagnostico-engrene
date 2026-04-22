<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: validate-squad-deterministic
  task_name: Validate Squad - Deterministic Checks
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
  - Detectar tipo do squad
  - Validar estrutura e configuracao
  - Executar scan de seguranca
  - Analisar cobertura operacional
  acceptance_criteria:
  - O tipo do squad e determinado usando sinais observaveis, nao intuicao
  - Squads sem config.yaml ou sem entrypoint sao bloqueados
  - Achados criticos de seguranca bloqueiam a validacao
  - Checklist coverage e orphan detection sao medidos explicitamente
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


# Task: Validate Squad - Deterministic Checks

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `validate-squad-deterministic` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: validate-squad-deterministic
name: "Validate Squad Deterministic Checks"
category: validation
agent: squad-chief
elicit: false
autonomous: true
description: "Consolida os 4 gates deterministas (type-detect, structure, security, coverage) em uma unica task Worker que le arquivos e produz pass/fail."
consolidates:
  - validate-squad-type-detect
  - validate-squad-structure
  - validate-squad-security
  - validate-squad-coverage
```

## Purpose

Executar todos os checks deterministas do squad em sequencia: detectar tipo, validar estrutura, escanear seguranca e medir cobertura. Cada step produz output consumivel pelos steps seguintes e pelas tasks posteriores (cross-references, quality, contextual, verdict).

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
  type_override:
    type: string
    required: false
```

## Workflow / Steps

### Step 1: Type Detection

Identificar se o squad e do tipo `expert`, `pipeline` ou `hybrid` usando sinais estruturais reais do diretorio, sem inferencia livre.

#### 1.1 Coletar sinais

- Contar arquivos em `agents/`, `tasks/` e `workflows/`.
- Verificar presenca de `voice_dna`, `behavioral_states`, heuristicas e organizacao por tiers.
- Verificar se o squad depende fortemente de workflow/orchestrator.

#### 1.2 Aplicar regras de classificacao

```yaml
signals:
  expert:
    - "voice_dna presente em agentes"
    - "nomes de especialistas reais ou personas densas"
    - "organizacao por tiers orientada a especialistas"
  pipeline:
    - "workflows dominam a operacao"
    - "um orquestrador central coordena fases"
    - "tasks > agents * 3"
  hybrid:
    - "mistura de heuristicas, personas e pipelines"
    - "behavioral_states presentes"
    - "executor/fallback logic presente"
```

#### 1.3 Resolver empate

- `type_override` vence, se fornecido.
- Empate entre `expert` e `pipeline`: preferir `pipeline` quando o fluxo for o centro da operacao.
- Empate entre `pipeline` e `hybrid`: preferir `hybrid` quando houver heuristicas formais.

### Step 2: Structure Validation

Executar o gate estrutural bloqueante antes de qualquer analise qualitativa.

#### 2.1 Validar configuracao

- Confirmar que `config.yaml` existe e parseia.
- Verificar campos minimos: `name`, `version`, `description`.
- Validar convencoes basicas de nome e versao.

#### 2.2 Validar entrypoint

- Verificar que o agente principal existe em `agents/`.
- Confirmar que o entrypoint tem `activation-instructions`.
- Verificar que o comando de ajuda existe ou que o agente tenha menu equivalente.

#### 2.3 Validar estrutura minima

- `agents/` e obrigatorio.
- `tasks/`, `workflows/`, `checklists/` e `templates/` sao exigidos quando houver referencias a eles.
- `config/` e `schemas/` sao esperados quando o squad declara validacao formal.

**Gate:** Squads sem `config.yaml` ou sem entrypoint => `ABORT`.

### Step 3: Security Scan

Isolar o scan de seguranca como gate proprio para que qualquer exposicao de segredos interrompa a validacao imediatamente.

#### 3.1 Procurar segredos bloqueantes

- API keys e tokens.
- Senhas e segredos hardcoded.
- Credenciais cloud e chaves privadas.
- URLs de banco com credenciais.
- Arquivos `.env`, `credentials*.json`, `service-account*.json`.

#### 3.2 Marcar warnings nao bloqueantes

- Uso de `eval`/`exec`.
- Artefatos sensiveis que exijam revisao manual.

#### 3.3 Produzir resultado do gate

- Qualquer achado critico => `ABORT`.
- Warnings nao bloqueiam, mas entram no relatorio final.

### Step 4: Coverage Analysis

Verificar se o squad cobre o proprio escopo de forma minimamente sustentavel.

#### 4.1 Cobertura de checklists

- Calcular `checklists / tasks_complexas`.
- Usar threshold bloqueante quando a cobertura ficar abaixo do minimo aceito.

#### 4.2 Cobertura de tasks e fases

- Detectar tasks orfas.
- Para squads `pipeline`, validar se toda fase relevante tem suporte operacional.

#### 4.3 Cobertura de dados e integracoes

- Medir uso de arquivos em `data/`.
- Validar `data/tool-registry.yaml` quando aplicavel.
- Cruzar referencias de servicos contra o `service-catalog` central quando existirem.

## Output

```yaml
output:
  schema:
    type_classification:
      detected_type: "expert | pipeline | hybrid"
      confidence: 0.0
      signals:
        agents_count: N
        tasks_count: N
        workflows_count: N
        voice_dna_present: true
        heuristics_present: true
      requirements_profile:
        required_components: []
        veto_family: []
    structure_report:
      status: "PASS | ABORT"
      config_valid: true
      entry_agent_exists: true
      entry_agent_activatable: true
      missing_directories: []
      blocking_issues: []
    security_report:
      status: "PASS | ABORT"
      critical_count: N
      warning_count: N
      critical_findings: []
      warnings: []
    coverage_report:
      status: "PASS | ABORT | WARN"
      metrics:
        checklist_coverage: "0%"
        orphan_tasks: 0
        phase_coverage: "N/A"
        data_usage: "0%"
        tool_registry: "PASS | WARN | N/A"
        service_catalog_compliance: "PASS | WARN | FAIL | N/A"
      issues: []
```

## Acceptance Criteria

- [ ] O tipo do squad e determinado usando sinais observaveis, nao intuicao
- [ ] `type_override` e respeitado quando informado
- [ ] O output inclui confianca e justificativa resumida
- [ ] Squads sem `config.yaml` ou sem entrypoint sao bloqueados
- [ ] Diretorios exigidos por referencias existentes sao validados
- [ ] Achados criticos de seguranca bloqueiam a validacao
- [ ] Warnings sao preservados para o relatorio final
- [ ] Checklist coverage e orphan detection sao medidos explicitamente
- [ ] Pipeline squads recebem validacao de cobertura por fases
- [ ] Falhas bloqueantes sao separadas de warnings

## Related Documents

- `validate-squad.md`
- `validate-squad-cross-references.md`
- `validate-squad-contextual.md`
- `validate-squad-verdict.md`
- `checklists/quality-gate-checklist.md`
- `squads/squad-creator/data/squad-type-definitions.yaml`
- `data/tool-registry.yaml`
