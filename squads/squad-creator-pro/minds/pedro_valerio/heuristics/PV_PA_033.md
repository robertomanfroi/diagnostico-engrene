---
id: "PV_PA_033"
title: "Executor Transversality"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Execution Assignment"
  - "Structural Integrity"
pipeline_instances:
  - "executor-assignment"
sys_tension:
  tension_with: "Executor Capability Variance"
  resolution: "Maintain invariant Molecule structure while abstracting capability negotiation to a separate configuration layer (executor-capabilities-map). Define Handoffs and Quality Gates in executor-agnostic terms; delegate execution mode selection to runtime capability matching."
---

# PV_PA_033 - Executor Transversality

**Type:** Decision Heuristic
**Phase:** 2 (Structural Assembly)
**Agent:** @hybridOps:process-architect

## Purpose

The defining components of Sinkra structure (Handoffs, Quality Gates) remain functionally identical regardless of the Executor assigned. The Executor is a transversal attribute plugged in, not a reason to structurally mutate the workflow's shape.

## Configuration

```yaml
PV_PA_033:
  name: "Executor Transversality"
  phase: 2

  veto_conditions:
    - condition: "pipeline_blueprint_fundamentally_mutated_just_because_agent_is_used == true"
      action: "VETO - A Handoff is a Handoff. Swap the Executor attribute; maintain the Molecule."
```

## Application

**Process:** Ensure operational diagrams do not shatter into completely distinct models when swapping "Clerk" for "GPT-4". The structure remains intact; only the execution layer changes.

## Decision Tree

```
IF (Process mapping requires totally new flowcharts solely because Executor changed) 
THEN THE ARCHITECTURE ITSELF IS FLAWED AND UNSTABLE.
```

## Failure Modes

### Distinct Siloed Operations
- **Trigger:** Designing entirely bespoke, complex custom routing flowcharts specifically titled "Agent Process", treating modern tools as isolated shadow functions instead of integrating them into universal Molecules.

## Validation

✓ **Tension Identified:** Paradoxo entre invariância estrutural (Molecules idênticas) e variância de capacidades executoras (Clerk vs. GPT-4 vs. Humanos têm competências radicalmente diferentes).

✓ **Resolution Applied:** Segregação em dois níveis:
  - **L1 (Molecular Invariant):** Handoffs, Quality Gates, artefatos de decisão — estruturalmente imutáveis, executor-agnostic
  - **L2 (Capability Negotiation):** executor-capabilities-map determina qual executor pode satisfazer qual constraint, sem mutar a forma da Molecule

✓ **Implicação Operacional:** Um mesmo Handoff pode ser executado por GPT-4 em modo "evaluator" ou por Clerk em modo "form-filler", mas a estrutura do Handoff (input → validation → output) permanece constante.

✓ **Anti-Pattern Bloqueado:** Proibir "Agent Process" como categoria separada — toda execução usa a mesma estrutura, diferenciada apenas via atributo executor + capabilities-map.
