# AN_KE_019 - Bug de Produção → Módulo Shared

**Type:** Decision Heuristic
**Zone:** 🔥 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Incident → Systemic Protection
**Source:** [SOURCE: conversa Eudes 2026-03-29 sobre JSON mal-formado → json-validator.sh protege 14 runners]
**sys_tension:** (localized_fix_vs_systemic_module, h3_threshold_decision)

## Purpose

Quando um bug de produção aparece, perguntar "outros scripts têm o mesmo risco?" Se sim, a correção deve ser um módulo shared, não um fix pontual. Custo igual, blast radius de proteção Nx maior.

## Configuration

```yaml
AN_KE_019:
  name: "Bug → Módulo Shared"
  zone: "genialidade"
  trigger: "Bug de produção reportado"

  rule: |
    SE bug de produção aparece
    ENTÃO PERGUNTAR: "Outros scripts/runners têm o MESMO risco?"
    SE SIM (3+ afetados) → criar módulo shared, não fix pontual
    SE NÃO (isolado) → fix pontual OK

  rationale: |
    Custo de 1 módulo ≈ custo de 1 fix pontual
    Mas proteção de 1 módulo = N scripts protegidos
    ROI cresce linearmente com número de consumidores

  evidence:
    - "Eudes: JSON mal-formado em 1 pipeline"
    - "Análise: 14 runners parsam JSON de LLM"
    - "Fix pontual: protege 1. json-validator.sh: protege 14"
    - "Custo: ~2h em ambos os casos"
    - "Funções: json_extract (4 strategies), json_validate, json_get, json_has_fields"

  tension_with: "AN_KE_007 (REUSE > CREATE) vs Quando criar módulo shared para bug sistêmico"
```

## Decision Tree

```
IF (production_bug_reported)
  THEN count affected_scripts = grep across codebase
    IF (affected_scripts >= 3)
      THEN create shared module (H3 threshold met)
      THEN integrate into all affected scripts
    ELSE IF (affected_scripts == 1)
      THEN fix pontual is OK
    ELSE (affected_scripts == 2)
      THEN fix pontual NOW, extract when 3rd appears (H3)
```

## Failure Modes

### O JSON que Derrubou 14 Runners
- **Trigger:** LLM gera JSON mal-formado. Sem json-validator.sh, 14 runners falhavam silenciosamente.
- **Manifestation:** Bug descoberto em 1 script → mesma vulnerabilidade em 14 outros.
- **Detection:** Eudes reportou JSON parsing error no pipeline.
- **Prevention:** Bug em 1 script + afeta N scripts = shared module. json-validator.sh protege todos 14.

## Validation

**Paradoxo Identificado:** Custo de criação (1 módulo shared) ≈ Custo de fix pontual. Mas impacto de proteção é assimétrico: **1 fix protege 1 runner** vs **1 módulo protege 14 runners**. A decisão não é econômica (custo), é estratégica (cobertura de risco). O H3 threshold (3+ afetados) é o ponto de inflexão onde a assimetria justifica o investimento.

**Resolução:** When cost is equal, blast radius of protection determines the decision. Systemic protection always wins over localized fixes when N ≥ 3.
