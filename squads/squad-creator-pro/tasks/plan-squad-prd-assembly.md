# Task: Plan Squad PRD Assembly

**Task ID:** plan-squad-prd-assembly
**Execution Type:** Agent
**Purpose:** montar o PRD final e o resumo de runtime a partir dos artefatos já decididos

## Inputs

- `planning_contract`
- `depth_rules`
- `domain_map`
- `architecture_package`
- `challenge_report`
- `roadmap_package`

## Steps

1. Renderizar `docs/projects/{domain}/prd.md` a partir do template profundo.
2. Garantir cobertura de contexto, capabilities, arquitetura, governança, roadmap, riscos e open questions.
3. Serializar `.aiox/squad-runtime/plan-squad/{domain}/planning-summary.yaml`.
4. Marcar handoff pronto para `*create-squad {domain}`.

## Output

```yaml
plan_squad:
  domain: "{domain}"
  output_path: "docs/projects/{domain}/prd.md"
  workflows_mapped: 0
  epics_planned: 0
  alternatives_compared: 0
  handoff_ready: true
```

## Veto

- PRD montado sem roadmap, governança ou open questions
