# Task: Plan Squad Architecture

**Task ID:** plan-squad-architecture
**Execution Type:** Agent
**Purpose:** definir tese do squad, arquitetura de agentes, knowledge model e governança

## Inputs

- `capability_map`
- `workflow_inventory`
- `risk_inputs`

## Steps

1. Definir a tese do squad e a diferença estratégica que ele cria.
2. Projetar orchestrator, tiers, handoffs e workflow-to-agent coverage.
3. Definir knowledge model, artefatos canônicos e fontes de verdade.
4. Definir quality gates, checkpoints humanos, vetoes e anti-patterns.
5. Emitir `agent_architecture`, `knowledge_model` e `governance_contract`.

## Output

```yaml
architecture_package:
  squad_thesis: ""
  agent_architecture: {}
  knowledge_model: {}
  governance_contract: {}
```

## Veto

- arquitetura sem governança explícita
- PRD profundo sem knowledge model ou fontes de verdade
