# AN_KE_042 - Don't Regress Working Code

**Type:** Development Discipline Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Preservar o que Funciona
**Source:** [SOURCE: Múltiplas sessões mmos — frustração recorrente com AI revertendo código funcional]

## Purpose

A IA tem tendência de "melhorar" código que já funciona, introduzindo regressões. Se algo funciona em localhost, a prioridade é PRESERVAR, não refatorar. Mudanças devem ser aditivas, nunca destrutivas sobre funcionalidade existente.

## Configuration

```yaml
AN_KE_042:
  name: "Don't Regress Working Code"
  zone: "excelencia"
  trigger: "IA propondo refatoração, simplificação, ou 'melhoria' de código existente."

  rule: |
    SE código funciona em localhost/prod
    ENTÃO preservar. Mudanças aditivas, nunca destrutivas.
    SE simplificação proposta → testar ANTES de aplicar.
    SE regressão detectada → git revert imediato, não tentar consertar em cima.

  sys_tension:
    tension_with: "AN_KE_085 (Greenfield Over Spaghetti Refactor) — Refactoring vs Preservation"
    resolution: "Default to PRESERVE when functionality works. Only REFACTOR when explicitly required for new feature integration. Always TEST before applying changes. If regression occurs, REVERT immediately and analyze surgically."

  veto_condition:
    trigger: "IA refatorando algo que estava funcionando sem garantir que continua funcionando."
    action: "VETO — 'tava funcionando, pq está revertendo algo que estava funcionando?'"

  evidence:
    - "[SOURCE: sessão mmos 435f78cd] 'tava funcionando localhost, pq está revertendo algo que estava funcionando?'"
    - "[SOURCE: sessão mmos 9701cc32] 'Continua puxando do banco de dados... basta reverter no git, no git tá funcionando'"
    - "[SOURCE: sessão mmos c61a9260] 'vamos reverter essa simplificação'"
    - "[SOURCE: sessão mmos cfecb27d] 'ta errado usar slug, o certo é usar o nome real do arquivo e trazendo a URL direto do banco'"
```

## Decision Tree

```javascript
IF (ai_proposes_refactor OR simplification)
  IF (current_code_works_in_localhost)
    THEN DEFAULT = PRESERVE
    IF (refactor_is_critical for new feature)
      THEN TEST_FIRST before applying
    ELSE
      THEN SKIP refactor — "if it works, don't touch it"
  IF (regression_detected_after_change)
    THEN IMMEDIATE git revert
    THEN ANALYZE what broke
    THEN RE-APPLY surgically (not the whole refactor)
```

## Failure Modes

### A Melhoria que Quebra
- **Trigger:** IA decide "simplificar" lógica de URL de imagens trocando campo real por slug derivado.
- **Manifestation:** Imagens param de carregar. Slug não corresponde ao nome real do arquivo.
- **Detection:** "ta errado usar slug, o certo é usar o nome real do arquivo".
- **Recovery:** git revert + restaurar lógica original.
- **Prevention:** Nunca substituir campo real (image_url) por campo derivado (slug) sem testar.

## Integration with Workflow

```yaml
checkpoint:
  id: "regression-prevention-gate"
  heuristic: AN_KE_042
  phase: "Code_Review / Refactoring"
```

## Validation

**Paradox Identified:** The tension between code optimization (refactoring) and system stability (preservation of working functionality) is inherent to this heuristic. The resolution enforces a conservative bias: when functionality works, optimization is deferred unless explicitly required by new features. This prevents the error pattern where "improvements" introduce silent regressions.

**Application Criteria:**
- ✓ Code executes correctly in localhost/staging
- ✓ Existing tests pass without modification
- ✓ No performance degradation observed
- ✓ No security vulnerabilities exploited

**Validation Triggers:**
1. If AI proposes refactoring → require BEFORE/AFTER test evidence
2. If regression detected → mandatory git revert + root cause analysis
3. If refactor is feature-critical → apply surgical changes only, not full refactors
