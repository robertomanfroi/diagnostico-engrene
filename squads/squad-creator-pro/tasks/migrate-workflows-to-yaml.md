<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: migrate-workflows-to-yaml
  task_name: Migrate Workflows to YAML (Stub)
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
  - Analyze Legacy Workflows
  - Convert and Validate YAML
  - Archive Originals and Cleanup References
  acceptance_criteria:
  - todos os workflows alvo são convertidos para .yaml com estrutura válida
  - workflows/ mantém apenas .yaml fora de _archive/
  - originais .md são preservados em workflows/_archive/
  - o wrapper não reimplementa localmente análise, conversão ou archive
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
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


# Task: Migrate Workflows to YAML (Stub)

**Task ID:** `migrate-workflows-to-yaml`  
**Version:** 3.1.0  
**Purpose:** compor a migração de workflows legados para `.yaml` via subtasks explícitas, sem manter instruções monolíticas no wrapper

## Canonical Sub-Tasks

- `migrate-workflows-analyze.md`
- `migrate-workflows-convert.md`
- `migrate-workflows-archive.md`

## Inputs

- diretório-alvo contendo workflows `.md`
- `workflow-tmpl.yaml` ou template equivalente aceito pelo squad
- regras de naming para `wf-{workflow-id}.yaml`

## Preconditions

- [ ] `migrate-workflows-analyze.md`, `migrate-workflows-convert.md` e `migrate-workflows-archive.md` existem
- [ ] o template de workflow em YAML existe antes da conversão
- [ ] o chamador entende que o archive só ocorre depois da validação do YAML convertido

## Execution Sequence

```text
[1] migrate-workflows-analyze
    extrai estrutura, gaps e readiness de cada workflow legado
[2] migrate-workflows-convert
    converte para .yaml, valida sintaxe e required fields
[3] migrate-workflows-archive
    arquiva .md originais, atualiza referências e verifica cleanup
OUTPUT: workflows .yaml válidos + _archive/ reconciliado
```

## Output

```yaml
output:
  analysis_artifact: "migration_analysis"
  conversion_artifact: "conversion_results"
  archive_artifact: "archive_results"
  final_state:
    workflows_root: "only .yaml outside _archive/"
    originals_preserved: true
```

## Acceptance Criteria

- [ ] todos os workflows alvo são convertidos para `.yaml` com estrutura válida
- [ ] `workflows/` mantém apenas `.yaml` fora de `_archive/`
- [ ] originais `.md` são preservados em `workflows/_archive/`
- [ ] o wrapper não reimplementa localmente análise, conversão ou archive
