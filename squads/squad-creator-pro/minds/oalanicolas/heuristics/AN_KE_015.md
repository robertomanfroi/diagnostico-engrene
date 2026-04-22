# AN_KE_015 - Fallback Graceful É Non-Negotiable

**Type:** Veto Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Dependency Safety
**Source:** [SOURCE: Epic 71 — todos 7 módulos v2 têm RUNNER_LIB_*=true/false + fallback inline]
**sys_tension:** (shared_dependency, graceful_fallback, "Módulos compartilhados devem ser reutilizáveis mas nunca podem quebrar o consumidor — resolver via availability flag + fallback inline")

## Purpose

Módulo shared nunca pode ser dependência hard. Se o módulo não carregar, o script deve continuar com comportamento degradado mas funcional.

## Configuration

```yaml
AN_KE_015:
  name: "Fallback Graceful"
  zone: "excelencia"
  trigger: "Criando módulo shared / integrando dependência"

  rule: |
    SE criando módulo shared
    ENTÃO flag de disponibilidade (MODULE_NAME=true/false)
    E branch condicional no consumidor
    E fallback inline quando módulo indisponível
    NUNCA hard dependency — script DEVE funcionar sem o módulo

  veto_condition:
    trigger: "Módulo sem fallback"
    action: "VETO — adicionar fallback antes de merge"

  pattern: |
    # No módulo:
    MODULE_FLAG=true

    # No consumidor:
    if [[ "${MODULE_FLAG:-false}" == "true" ]]; then
      use_shared_function
    else
      inline_fallback
    fi

  evidence:
    - "validate-skill.sh funciona SEM validator-lib (fallback inline para cores, scoring, security)"
    - "sinkra-map.sh funciona SEM pipeline-bootstrap (fallback para source lib/runtime.sh)"
    - "12 flags de disponibilidade no pipeline-bootstrap.sh"

  tension_with: "AN_KE_013 (Regra dos 3+ Consumidores) — Módulos compartilhados ganham complexidade de fallback, mas tornam-se resilientes em vez de rígidos"
```

## Decision Tree

```javascript
IF (creating_shared_module)
  REQUIRE: availability flag (MODULE_NAME=true/false)
  REQUIRE: consumer checks flag before using module
  REQUIRE: inline fallback when flag=false
  TEST: script must work with MODULE_FLAG=false
  NEVER: hard import without availability check
```

## Failure Modes

### O Pipeline que Quebrou no CI
- **Trigger:** Shared module not available in CI environment (different PATH, missing dep).
- **Manifestation:** `source: file not found` → pipeline abort.
- **Detection:** CI fails but local passes.
- **Prevention:** Flag check + inline fallback. CI runs with MODULE_FLAG=false automatically.

---

## Validation

✅ **Paradoxo identificado:** Compartilhamento (reutilização) vs Independência (resiliência)

✅ **Resolução:** Opcionais via availability flags + fallbacks inline garantem que o consumidor funciona sempre, com ou sem o módulo compartilhado

✅ **Evidência:** 12 flags de disponibilidade no pipeline-bootstrap.sh + 7 módulos v2 com RUNNER_LIB_*=true/false

✅ **Teste:** Scripts executam com MODULE_FLAG=false sem falhas

✅ **Status:** Veto habilitado para módulos sem fallback
