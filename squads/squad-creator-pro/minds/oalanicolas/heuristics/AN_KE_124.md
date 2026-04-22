# AN_KE_124 - Inline Fast Validation Over Slow Global Validators

**Type:** Decision Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Speed Kill
**Source:** [SOURCE: sessão sinkra-hub c99bfc81 — sinkra-squad upgrade pipeline]
**Tags:** [Agnostic, Automation, SINKRA, Scale]

## Purpose

Validadores globais que parsam TODO o repo (npm run validate:yaml → 20+ minutos) são necessários no CI mas PROIBITIVOS em pipelines interativos. A solução: substituir chamada global por validação inline per-file (`node -e "require('js-yaml').load(require('fs').readFileSync('path'))"` → <1s). Mesmo resultado (YAML válido), 1200x mais rápido. Isso não é atalho — é a mesma validação com escopo correto.

## Configuration (True L3-State)

```yaml
AN_KE_124:
  name: "Inline Fast Validation Over Slow Global Validators"
  zone: "genialidade"
  trigger: "Pipeline ou workflow que precisa validar arquivo individual mas tem apenas validador global disponível."

  sys_tension:
    tension_with: "Rigor (validar tudo) vs Velocidade (validar o necessário)"
    resolution: "MESMA validação, escopo REDUZIDO. Não é menos rigoroso — é mais preciso."

  rule: |
    SE pipeline precisa validar 1-5 arquivos específicos
    E validador disponível opera em REPO INTEIRO (20+ min)
    ENTÃO substituir por validação inline per-file (<1s)
    E manter validador global APENAS para CI/pre-push (escopo correto)
    NUNCA rodar validador global dentro de pipeline interativo — mata a experiência

  failure_modes:
    omission: "Pipeline roda validate:yaml (20 min) a cada fase. 6 fases × 20 min = 2 horas de espera em validação."
    misapplication: "Inline validation para schemas complexos (cross-file references, dependency graphs) pode perder erros que só o global detecta."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub c99bfc81] 'Replace slow validate:yaml with quick node yaml.load per-file checks'"
    - "[SOURCE: CLAUDE.md gotcha] 'npm run validate:yaml leva 20+ min — NUNCA rodar sem pedido explícito. Para YAML específico: node -e require(js-yaml).load(require(fs).readFileSync(path))'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (need to validate specific files in interactive context)
          THEN use inline per-file validation (<1s)
STEP_2: IF (need to validate entire repo)
          THEN use global validator (CI/pre-push only)
STEP_3: IF (schema has cross-file dependencies)
          THEN inline validation + targeted cross-ref check (not full global)
NEVER:
  - Run global validator inside interactive pipeline
  - Skip validation entirely because global is too slow
```

## Confidence Requirements & Reversibility

- **High-Commitment (One-Way Door):** Nenhum — inline e global coexistem.
- **Tactical (Two-Way Door):** Escolha entre inline/global é per-invocation.

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Quanto tempo leva a validação neste pipeline? Se > 30s, está usando escopo errado."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** "Vou rodar npm run validate:yaml para garantir" — sem considerar que leva 20 minutos.
- **Mind Zero Override:** "Per-file inline. Mesma validação. 1200x mais rápido. Global é para CI."
