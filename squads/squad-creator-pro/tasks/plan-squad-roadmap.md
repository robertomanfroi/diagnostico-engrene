# Task: Plan Squad Roadmap

**Task ID:** plan-squad-roadmap
**Execution Type:** Agent
**Purpose:** derivar épicos, stories e quality gates a partir da arquitetura validada

## Inputs

- `challenge_report`
- `alternatives_matrix`
- `sequencing_rationale`

## Steps

1. Agrupar trabalho em épicos coerentes.
2. Quebrar cada épico em stories executáveis.
3. Definir quality gates e critérios de readiness por épico.
4. Relacionar dependências e riscos por bloco.
5. Emitir `roadmap` e `quality_gate_matrix`.

## Output

```yaml
roadmap_package:
  epics: []
  stories: []
  quality_gate_matrix: []
```

## Veto

- roadmap sem gates ou sem dependências explícitas
