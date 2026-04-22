# Task: Plan Squad Contract

**Task ID:** plan-squad-contract
**Execution Type:** Agent
**Purpose:** fechar o contrato mínimo do planejamento antes de qualquer síntese profunda

## Inputs

- `domain`
- `purpose` opcional
- `target_user` opcional
- `output` opcional
- `reference` opcional

## Steps

1. Resolver `output_path` e `reference_path`.
2. Definir `problem_statement`, `purpose` e `target_user` com evidência local.
3. Marcar inferências fracas explicitamente como `assumption`.
4. Emitir `planning_contract` e `environment_contract`.

## Output

```yaml
planning_contract:
  domain: "{domain}"
  problem_statement: "..."
  purpose: "..."
  target_user: "..."
  output_path: "docs/projects/{domain}/prd.md"
  reference_path: "{path|null}"
  desired_depth: "deep"
```

## Veto

- problema não articulado e sem evidência defensável
- output path indefinido
