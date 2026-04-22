# Task: Plan Squad Depth Calibration

**Task ID:** plan-squad-depth-calibration
**Execution Type:** Agent
**Purpose:** calibrar profundidade usando template e benchmark sem copiar ontologia alheia

## Inputs

- `planning_contract`
- `squads/squad-creator-pro/templates/squad-prd-deep-tmpl.md`
- `squads/squad-creator-pro/data/pm-best-practices.md`
- `reference_path` opcional

## Steps

1. Ler template e best practices.
2. Se houver benchmark, extrair só profundidade estrutural, não taxonomia de domínio.
3. Registrar elementos universais versus específicos do benchmark.
4. Emitir `depth_rules` e `reference_delta`.

## Output

```yaml
depth_calibration:
  depth_rules: []
  reference_delta:
    reusable_patterns: []
    forbidden_domain_carryover: []
```

## Veto

- benchmark copiado literalmente
- depth calibration sem separação entre forma e conteúdo
