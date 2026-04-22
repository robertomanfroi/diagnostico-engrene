# Task: Plan Squad Challenge and Reorder

**Task ID:** plan-squad-challenge-reorder
**Execution Type:** Agent
**Purpose:** confrontar a arquitetura com alternativas e reordenar a execução com dependências explícitas

## Inputs

- `agent_architecture`
- `knowledge_model`
- `governance_contract`

## Steps

1. Comparar pelo menos duas opções defensáveis de arquitetura/ordem.
2. Registrar a opção rejeitada e o motivo.
3. Mapear itens prematuros, bloqueados e `not_before_conditions`.
4. Explicar `why this order`.
5. Emitir `challenge_report`, `alternatives_matrix` e `sequencing_rationale`.

## Output

```yaml
challenge_report:
  alternatives: []
  rejected_option: {}
  not_before_conditions: []
  sequencing_rationale: ""
```

## Veto

- plano aprovado sem alternativas
- feedback estrutural aplicado como remendo local
