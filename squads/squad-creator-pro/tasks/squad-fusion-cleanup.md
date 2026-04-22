<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: squad-fusion-cleanup
  task_name: Squad Fusion - Cleanup
  status: pending
  responsible_executor: '@squad-chief'
  execution_type: Human
  estimated_time: 1h
  domain: Tactical
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Verificar pré-condições
  - Executar cleanup opcional
  acceptance_criteria:
  - Cleanup nunca ocorre sem aprovação compatível com o modo [threshold: >= 1]
  - Sources são preservados quando `keep_sources=true [threshold: >= 1]
  - O fechamento final mantém trilha de rollback [threshold: >= 1]
  output_persistence: transient_output
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Strategic
  atomic_layer: Atom
  executor: Human
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Squad Fusion - Cleanup

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-fusion-cleanup` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Human` |

## Metadata

```yaml
id: squad-fusion-cleanup
name: "Squad Fusion Cleanup"
category: fusion
agent: squad-chief
elicit: true
autonomous: false
description: "Executa a limpeza final opcional da fusão, respeitando quality gates, rollback path e confirmação humana para ações destrutivas."
```

## Purpose

Executar cleanup apenas quando a fusão estiver estável e houver confirmação apropriada para ações irreversíveis.

## Workflow / Steps

### Step 1: Verificar pré-condições

- Confirmar quality gates aprovados.
- Confirmar rollback path pronto.
- Respeitar `keep_sources`.

### Step 2: Executar cleanup opcional

- Arquivar ou remover squads fonte somente quando aprovado.
- Limpar workspace temporário e fechar o audit log.

## Output

```yaml
output:
  schema:
    sources_removed: []
    final_status: "completed | completed_with_sources_kept"
```

## Acceptance Criteria

- [ ] Cleanup nunca ocorre sem aprovação compatível com o modo [threshold: >= 1]
- [ ] Sources são preservados quando `keep_sources=true` [threshold: >= 1]
- [ ] O fechamento final mantém trilha de rollback [threshold: >= 1]
